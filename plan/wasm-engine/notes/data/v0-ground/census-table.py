# V0 item 1: one table from the three census outputs.
#   python3 -I census-table.py > census-table.txt     (in this directory)
import re
runs = [("slides", "census-slides.out"), ("tex input.tex", "census-tex.out"), ("tex deck", "census-tex-deck.out")]
counts, totals = {}, {}
for name, f in runs:
    for line in open(f, errors="replace"):
        m = re.match(r"CENSUS\s+(\d+) (\S+)", line)
        if m:
            counts.setdefault(m.group(2), {})[name] = int(m.group(1))
        m = re.match(r"CENSUS-TOTAL (\d+) rule applications, (\d+) of (\d+)", line)
        if m:
            totals[name] = (int(m.group(1)), int(m.group(2)))
rules = sorted(counts, key=lambda r: -max(counts[r].values()))
print("%-44s %12s %14s %14s" % ("rule function", *[n for n, _ in runs]))
for r in rules:
    print("%-44s %12s %14s %14s" % (r, *[counts[r].get(n, "") for n, _ in runs]))
print("%-44s %12d %14d %14d" % ("rule applications", *[totals[n][0] for n, _ in runs]))
print("%-44s %12d %14d %14d" % ("rule functions", *[totals[n][1] for n, _ in runs]))
print("rule functions in the union: %d" % len(rules))
