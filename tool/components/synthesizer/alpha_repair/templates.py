from . import simple_template
from ..template import Template, Insertion, MASK_TOKEN
import abc


class Base(Template):
    @classmethod
    @abc.abstractmethod
    def enumerate_masked_lines(cls, faulty_line, tokenizer):
        pass

    @classmethod
    def enumerate(
        cls, source_path, faulty_line_loc, faulty_line, sbfl_score, tokenizer
    ):
        templates = []
        masked_lines = cls.enumerate_masked_lines(faulty_line, tokenizer)
        for masked_line in masked_lines:
            templates.append(
                cls(
                    source_path,
                    faulty_line_loc,
                    faulty_line,
                    sbfl_score,
                    masked_line.strip(),
                )
            )
        return templates


class ReplacementTemplate(Base):
    pass


class AddNewLineBefore(Base, Insertion):
    @classmethod
    def enumerate_masked_lines(cls, faulty_line, tokenizer):
        return [" " + MASK_TOKEN * token_len + " " for token_len in range(1, 30)]


class LineReplacement(ReplacementTemplate):
    @classmethod
    def enumerate_masked_lines(cls, faulty_line, tokenizer):
        masked_lines = []
        fault_line_token_size = (
            tokenizer(faulty_line, return_tensors="pt")["input_ids"].shape[1] - 2
        )

        # Straight up line replacement
        for token_len in range(
            fault_line_token_size - 5, fault_line_token_size + 5
        ):  # Within 10
            if token_len <= 0:
                continue
            masked_lines.append(" " + MASK_TOKEN * token_len + " ")
        return masked_lines


class PartialTemplate(ReplacementTemplate):
    @classmethod
    def enumerate_masked_lines(cls, faulty_line, tokenizer):
        masked_lines = []
        for partial_beginning, partial_end in simple_template.generate_template(
            faulty_line
        ):
            for token_len in range(2, 11):
                if token_len <= 0:
                    continue
                masked_line = (
                    " " + partial_beginning + MASK_TOKEN * token_len + partial_end + " "
                )
                masked_lines.append(masked_line)
        return masked_lines


class MatchTemplate(ReplacementTemplate):
    def __init__(
        self, source_path, faulty_line_loc, faulty_line, sbfl_score, masked_line, match
    ):
        super().__init__(
            source_path, faulty_line_loc, faulty_line, sbfl_score, masked_line
        )
        self.match_splits = match.split(MASK_TOKEN)

    def recover(self, tok_predictions):
        if len(self.match_splits) == 2:
            return (
                self.match_splits[0] + "".join(tok_predictions) + self.match_splits[1]
            )
        else:
            index = 0
            gen_line = ""
            for c in self.masked_line.split(MASK_TOKEN)[:-1]:
                gen_line += c
                gen_line += tok_predictions[index]
                index += 1
            gen_line += self.masked_line.split(MASK_TOKEN)[-1]
            gen_line = gen_line[1:-1]
            return gen_line

    def adjust_score(self, score):
        if len(self.match_splits) == 2:
            return super().adjust_score(score)
        else:
            return score / (self.token_len * len(self.match_splits) - 1)

    @classmethod
    def enumerate_masked_lines(cls, faulty_line, tokenizer):
        pass

    @classmethod
    def enumerate(
        cls, source_path, faulty_line_loc, faulty_line, sbfl_score, tokenizer
    ):
        templates = []
        for match, length in simple_template.generate_match_template(
            faulty_line, tokenizer
        ):
            for token_len in range(1, length + 5):
                if len(match.split(MASK_TOKEN)) == 2:
                    masked_line = (
                        " "
                        + match.split(MASK_TOKEN)[0]
                        + MASK_TOKEN * token_len
                        + match.split(MASK_TOKEN)[1]
                        + " "
                    )
                else:
                    masked_line = " "
                    masked_line += (MASK_TOKEN * token_len).join(
                        match.split(MASK_TOKEN)
                    ) + " "
                templates.append(
                    cls(
                        source_path,
                        faulty_line_loc,
                        faulty_line,
                        sbfl_score,
                        masked_line,
                        match,
                    )
                )
        return templates


class SimpleOperator(ReplacementTemplate):
    def recover(self, tok_predictions):
        index = 0
        gen_line = ""
        for c in self.masked_line.split(MASK_TOKEN)[:-1]:
            gen_line += c
            gen_line += tok_predictions[index]
            index += 1
        gen_line += self.masked_line.split(MASK_TOKEN)[-1]
        gen_line = gen_line[1:-1]
        return gen_line

    @classmethod
    def enumerate_masked_lines(cls, faulty_line, tokenizer):
        masked_lines = []
        for template in simple_template.match_simple_operator(faulty_line, tokenizer):
            masked_line = " " + template + " "
            masked_lines.append(masked_line)
        return masked_lines
