from synthesizer.abspatch import AbsPatch
from ..abspatch import AbsPatch
from ..template import Template, Insertion, MASK_TOKEN
from javalang import tokenizer
import pprint
import abc

FL4APR_MASK_TOKEN = '"<FL4APR_MASK>"'
REPLACE_ME_TO_MASK = '"<MASK_ME>"'
REPLACE_ME_TO_SINGLE_MASK = '"<SINGLE_MASK_ME>"'
MAX_TOKEN_LEN = 10


class Base(Template):
    @classmethod
    @abc.abstractmethod
    def prepare_replacement(cls, rewritten_source, matched_part):
        pass

    @classmethod
    def enumerate(cls, p: AbsPatch):
        templates = []

        replacements = cls.prepare_replacement(p.rewritten_source, p.matched_part)
        for rep in replacements:
            masked_lines = []
            if REPLACE_ME_TO_MASK in (
                single_replaced := rep.replace(REPLACE_ME_TO_SINGLE_MASK, MASK_TOKEN)
            ):
                masked_lines.extend(
                    single_replaced.replace(REPLACE_ME_TO_MASK, n * MASK_TOKEN)
                    for n in range(1, MAX_TOKEN_LEN + 1)
                )
            else:
                masked_lines.append(single_replaced)

            templates.extend(
                cls(
                    p.key.source_path,
                    p.key.faulty_line_loc,
                    p.key.faulty_line,
                    p.key.sbfl_score,
                    masked_line,
                )
                for masked_line in masked_lines
            )

        return templates


class ReplacementTemplate(Base):
    @classmethod
    @abc.abstractmethod
    def mutate_matched_expression(cls, rewritten_source, matched_part) -> list[str]:
        pass

    @classmethod
    def prepare_replacement(cls, rewritten_source, matched_part):
        return [
            rewritten_source.replace(FL4APR_MASK_TOKEN, mutant)
            for mutant in cls.mutate_matched_expression(rewritten_source, matched_part)
        ]


class MutateCastingType(Base):
    @classmethod
    def prepare_replacement(cls, rewritten_source, matched_part):
        return [rewritten_source.replace(FL4APR_MASK_TOKEN, REPLACE_ME_TO_SINGLE_MASK)]


class MutateVarDeclType(Base):
    @classmethod
    def prepare_replacement(cls, rewritten_source, matched_part):
        return [rewritten_source.replace(FL4APR_MASK_TOKEN, REPLACE_ME_TO_SINGLE_MASK)]


class SimpleReplacement(ReplacementTemplate):
    @classmethod
    def mutate_matched_expression(cls, rewritten_source, matched_part):
        return [REPLACE_ME_TO_MASK]


class MutateCondition(ReplacementTemplate):
    @classmethod
    def mutate_matched_expression(cls, rewritten_source, matched_part):
        try:
            tokens = list(tok.value for tok in (tokenizer.tokenize(rewritten_source)))
        except:
            return []

        if not (tokens[0] in ["if", "&&", "||"]):
            return []

        return [
            f"{matched_part} && {REPLACE_ME_TO_MASK}",
            f"{REPLACE_ME_TO_MASK} || {matched_part}",
        ]


class MutateOperator(ReplacementTemplate):
    @classmethod
    def mutate_matched_expression(cls, rewritten_source, matched_part):
        try:
            # parenthesize expression to avoid parsing bug
            matched_tokens = list(tokenizer.tokenize(f"({matched_part})"))
        except:
            return []

        operators = [
            tok
            for tok in matched_tokens
            if isinstance(tok, tokenizer.Operator) and tok.is_infix()
        ]
        return [
            matched_part[: op.position.column - 2]
            + REPLACE_ME_TO_SINGLE_MASK
            + matched_part[op.position.column - 2 + len(op.value) :]
            for op in operators
        ]


class MatchTemplate(ReplacementTemplate):
    @classmethod
    def find_method_identifier(cls, tokens):
        candidates = filter(
            lambda i: isinstance(i[1], tokenizer.Identifier)
            and (i[0] == 0 or tokens[i[0] - 1].value == ".")
            and i[0] < len(tokens) - 1
            and tokens[i[0] + 1].value == "(",
            enumerate(tokens),
        )
        for idx, method_token in candidates:
            stack = []
            for tok in tokens[idx + 1 :]:
                if tok.value == "(":
                    stack.append(tok.value)
                elif tok.value == ")":
                    stack.pop()

                if stack == []:
                    if tok.position == tokens[-1].position:
                        return (idx, method_token)
                    else:
                        break
        return None

    @classmethod
    def mutate_matched_expression(cls, rewritten_source, matched_part):
        try:
            tokens = list(tokenizer.tokenize(matched_part))
        except:
            return []

        if (identifier := cls.find_method_identifier(tokens)) is None:
            return []

        idx, method_name = identifier
        tokens = [tok.value for tok in tokens]

        callee_replaced = tokens.copy()
        callee_replaced[: idx + 1] = REPLACE_ME_TO_MASK

        method_only = tokens.copy()
        method_only[idx] = REPLACE_ME_TO_MASK

        args_replaced = tokens.copy()
        args_replaced[idx + 1 :] = "(" + REPLACE_ME_TO_MASK + ")"
        return [
            "".join(tokens) for tokens in [callee_replaced, method_only, args_replaced]
        ]


class InsertHandle(Base, Insertion):
    @classmethod
    def prepare_replacement(cls, rewritten_source, matched_part):
        MASKED_RETURN = "return " + FL4APR_MASK_TOKEN
        return [
            rewritten_source.replace(
                MASKED_RETURN, ("return " + REPLACE_ME_TO_SINGLE_MASK)
            ).replace(FL4APR_MASK_TOKEN, REPLACE_ME_TO_MASK)
        ]


class SkipStmt(Base, Insertion):
    @classmethod
    def prepare_replacement(cls, rewritten_source, matched_part):
        return [rewritten_source.replace(FL4APR_MASK_TOKEN, REPLACE_ME_TO_MASK)]


class InsertMethodCall(Base, Insertion):
    @classmethod
    def prepare_replacement(cls, rewritten_source, matched_part):
        return [rewritten_source.replace(FL4APR_MASK_TOKEN, REPLACE_ME_TO_MASK)]
