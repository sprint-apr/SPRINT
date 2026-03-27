import abc
import time
from typing import List, Tuple

from .alpha_repair.bert_beam_search import BeamSearch
from transformers import (
    RobertaTokenizer,
    RobertaForMaskedLM,
    AutoModelForCausalLM,
    AutoTokenizer,
)


class Model(abc.ABC):
    def __init__(
        self, conf, tokenizer, token_size_counter, infill_token, max_token_size
    ):
        self.conf = conf
        self.tokenizer = tokenizer
        self.token_size_counter = token_size_counter
        self.infill_token = infill_token
        self.max_token_size = max_token_size

    @abc.abstractmethod
    def generate_beam_direct(self, template, prefix, suffix) -> List[Tuple[str, float]]:
        pass

    # return type of beam query is a tuple of a (change, proba) list and elapsed time )
    def generate_beam(
        self, template, prefix, suffix, bug_id, db_conn
    ) -> Tuple[List[Tuple[str, float]], float]:
        # result for query found in DB
        if result := self.load_from_db(template, bug_id, db_conn):
            return result

        t_begin = time.time()
        if (beam_list := self.generate_beam_direct(template, prefix, suffix)) is None:
            return None
        beam_time = time.time() - t_begin
        self.store_into_db(template, bug_id, db_conn, beam_list, beam_time)
        return beam_list, beam_time

    def load_from_db(self, template, bug_id, conn):
        cursor = conn.cursor()
        cursor.execute(
            f"""
            SELECT * FROM {bug_id}_results WHERE
                source_path = %s AND faulty_line_loc = %s AND is_insertion = %s AND masked_line = %s AND beam_size = %s
            """,
            (
                template.source_path,
                template.faulty_line_loc,
                str(template.is_insertion()),
                template.masked_line,
                self.conf.beam_width,
            ),
        )
        if result := cursor.fetchone():
            beam_results, beam_time = result[6], result[7]
            beam_list = []
            try:
                for beam_result in beam_results.split("@,"):
                    [patch_code, proba] = beam_result.split("@:")
                    beam_list.append((patch_code, float(proba)))
            except:
                # sometimes empty results are found from DB
                cursor.execute(
                    f"DELETE FROM {bug_id}_results WHERE id = %s", (result[0],)
                )
                return None
            return beam_list, float(beam_time)

        else:
            return None

    def store_into_db(self, template, bug_id, conn, beam_list, beam_time):
        cursor = conn.cursor()

        result = "@,".join(
            [f"{patch_code}@:{proba}" for (patch_code, proba) in beam_list]
        )
        data = {
            "source_path": template.source_path,
            "faulty_line_loc": template.faulty_line_loc,
            "is_insertion": str(template.is_insertion()),
            "masked_line": template.masked_line,
            "beam_size": self.conf.beam_width,
            "beam_results": result,
            "beam_time": beam_time,
        }
        cursor.execute(
            f"""
            INSERT INTO {bug_id}_results (source_path, faulty_line_loc, is_insertion, masked_line, beam_size, beam_results, beam_time)
            VALUES (%(source_path)s, %(faulty_line_loc)s, %(is_insertion)s, %(masked_line)s, %(beam_size)s, %(beam_results)s, %(beam_time)s)
        """,
            data,
        )
        conn.commit()


class CodeBert(Model):
    def __init__(self, conf):
        tokenizer = RobertaTokenizer.from_pretrained("microsoft/codebert-base-mlm")
        super().__init__(
            conf=conf,
            tokenizer=tokenizer,
            token_size_counter=lambda code: tokenizer(code, return_tensors="pt")[
                "input_ids"
            ].size()[1],
            infill_token="<mask>",
            max_token_size=512,
        )
        self.model = RobertaForMaskedLM.from_pretrained(
            "microsoft/codebert-base-mlm"
        ).to(conf.device)

    def generate_beam_direct(self, template, prefix, suffix) -> List[Tuple[str, float]]:
        input = prefix + template.masked_line + suffix
        if self.token_size_counter(input) >= self.max_token_size:
            return None
        beam_engine = BeamSearch(
            self.model,
            self.tokenizer,
            input,
            self.conf.device,
            self.conf.beam_width,
            re_rank=True,
        )

        beam_list, masked_index = beam_engine.generate_beam()
        return [
            (template.recover(codes), template.adjust_score(proba))
            for (proba, _, codes) in beam_list
        ]
