import abc
from dataclasses import dataclass

MASK_TOKEN = "<mask>"


@dataclass
class Template(abc.ABC):
    source_path: str
    faulty_line_loc: int
    faulty_line: str
    sbfl_score: float
    masked_line: str
    token_len: int | None = None

    def __post_init__(self):
        self.token_len = self.masked_line.count(MASK_TOKEN)

    def recover(self, tok_predictions):
        s: str = self.masked_line
        for pred in tok_predictions:
            s = s.replace(MASK_TOKEN, pred, 1)
        return s

    def adjust_score(self, score):
        return score / self.token_len

    def is_insertion(self):
        return isinstance(self, Insertion)


class Insertion:
    pass
