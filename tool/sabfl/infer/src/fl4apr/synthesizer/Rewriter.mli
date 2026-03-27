open! IStd
module F = Format

type application = {cmd: string; result: (replacement, string) Result.t}

and replacement = {rewritten_source: string; matched_part: string}

val apply : Patch.t -> application list
