#!/usr/bin/env python3
"""Per-command comparison of two spec-test result directories (engine plan E2).

  python3 compare-spec.py BEFORE_DIR AFTER_DIR

Each NAME.out holds the session of one script. The sequence of its
T7-TRY / T7-CMD lines is the per-command result. Prints the scripts whose
sequences differ; when one sequence is a prefix of the other (a script cut
by the time limit) it says so.
"""
import os
import re
import sys


def cmds(path):
    out = []
    for line in open(path, errors="replace"):
        line = re.sub(r"^.*!>+", "", line).rstrip()
        if line.startswith(("T7-TRY ", "T7-CMD ", "T7-DONE ", "T7-EXIT ")):
            out.append(line)
    return out


before, after = sys.argv[1], sys.argv[2]
names = sorted(f for f in os.listdir(before) if f.endswith(".out"))
same = prefix = differ = missing = 0
total = 0
for n in names:
    if not os.path.exists(os.path.join(after, n)):
        missing += 1
        print("missing after:", n)
        continue
    a, b = cmds(os.path.join(before, n)), cmds(os.path.join(after, n))
    ac = [x for x in a if x.startswith(("T7-TRY", "T7-CMD"))]
    bc = [x for x in b if x.startswith(("T7-TRY", "T7-CMD"))]
    k = min(len(ac), len(bc))
    total += sum(1 for x in ac[:k] if x.startswith("T7-CMD"))
    if ac == bc:
        same += 1
    elif ac[:k] == bc[:k]:
        prefix += 1
        print("prefix (time limit or crash):", n, "before", len(ac), "after", len(bc),
              "| end before:", a[-1], "| end after:", b[-1])
    else:
        differ += 1
        i = next(i for i in range(k) if ac[i] != bc[i])
        print("DIFFER:", n, "at", i, "|", ac[i], "|", bc[i])
print("scripts:", len(names), "same:", same, "prefix:", prefix, "differ:", differ, "missing:", missing)
print("commands with the same result in both runs:", total)
