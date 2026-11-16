#!/usr/bin/env python3
"""Compare two mode manifests (engine plan E2).

  git show 78d1584:translate/tests/sem-3.0/modes-3.0.lsp > before.lsp
  python3 compare-modes.py before.lsp ../../../../../translate/tests/sem-3.0/modes-3.0.lsp

Prints the functions whose mode got worse (must be none), how many got
better, and the modes of the functions that are new.
"""
import re
import sys
from collections import Counter

RANK = {"PROGRAM": 0, "LOGIC": 1, "GUARDS": 2}


def load(path):
    text = open(path).read()
    return {m.group(1): m.group(2) for m in re.finditer(r"\((\S+) \. :(\w+)\)", text)}


before, after = load(sys.argv[1]), load(sys.argv[2])
worse = [(k, before[k], after[k]) for k in before if k in after and RANK[after[k]] < RANK[before[k]]]
gone = [k for k in before if k not in after]
better = [k for k in before if k in after and RANK[after[k]] > RANK[before[k]]]
new = [k for k in after if k not in before]
print("functions before:", len(before), dict(Counter(before.values())))
print("functions after: ", len(after), dict(Counter(after.values())))
print("worse:", worse)
print("gone:", gone)
print("better:", len(better))
print("new:", len(new), dict(Counter(after[k] for k in new)))
print("new in :program:", sorted(k for k in new if after[k] == "PROGRAM"))
