# E0 item 3: shares of CPU time per kind of cost, from the sb-sprof graph
# reports in profile-raw.out (profile.lsp). Usage: python3 -I classify.py FILE
#
# Self samples are classified by function name. Samples in __bzero and
# _platform_memset (SBCL zeroing a fresh allocation region) are allocation:
# they are charged to the callers of __bzero in proportion to the caller
# counts of the graph, and reported both as "allocation" and by the class of
# the caller that allocated.
import re, sys
from collections import defaultdict

def cls(name):
    n = name
    if 'ACL2-COUNT' in n or '%SIZE' in n or n.endswith('TWO-ARG-+') or '%OM' in n:
        return 'termination check (%SIZE / ACL2-COUNT)'
    if re.search(r'STEP/R-CTXT|STEP/SEARCH|STEP/PREFIX|STEP/SPLIT', n):
        return 'contexts: STEP/R-CTXT-*, STEP/SEARCH* (split, rebuild)'
    if re.search(r'\$WITH_|\$MEM|BYTES|\$INV_|\$NBYTES|\$IBYTES|%UPD|%COMP|\$STORE|LOAD|STORE', n):
        return 'store and memory'
    if re.search(r'STEP_PURE|STEP_READ|STEP/R-|STEP\b|STEP$', n):
        return 'rule matching (rule functions, their SEARCH/MATCH helpers)'
    if n in ('TRUE-LISTP', 'TAKE', 'NTHCDR', 'LEN', 'APPEND', 'REVAPPEND', 'BINARY-APPEND', 'W3T::VAL-P') or 'TWO-ARG-<' in n or 'TWO-ARG->' in n or n.endswith('-P'):
        return 'list and shape tests (TRUE-LISTP, LEN, TAKE, *-P)'
    if n.startswith('Unknown fn'):
        # sb-sprof names no function of a mutual-recursion clique here. By
        # their callers and callees in the graph these are the relation
        # functions themselves (STEP_PURE: called by STEP/R-PURE, calls
        # every STEP_PURE/R-*; STEP: calls every STEP/R-*).
        return 'relation functions STEP, STEP_PURE, STEP_READ (unnamed in the profile)'
    if '$' in n or 'W3T::' in n:
        return 'other spec functions (numerics, aux)'
    return 'other (Lisp runtime)'

ALLOC = ('foreign function __bzero', 'foreign function _platform_memset')

def parse(block):
    # returns {name: self}, {callee: {caller: count}}
    selfc, callers = {}, defaultdict(dict)
    for ent in block.split('-' * 72):
        lines = [l for l in ent.split('\n') if l.strip()]
        prim = None; pending = []
        for l in lines:
            m6 = re.match(r'\s+(\d+)\s+[\d.]+\s+(\d+)\s+[\d.]+\s+(.*?) \[\d+\]$', l)
            m2 = re.match(r'\s+(\d+)\s+[\d.]+\s+(.*?) \[\d+\]$', l)
            if m6 and prim is None:
                prim = m6.group(3); selfc[prim] = int(m6.group(1))
                for c, k in pending: callers[prim][c] = k
            elif m2 and prim is None:
                pending.append((m2.group(2), int(m2.group(1))))
    return selfc, callers

text = open(sys.argv[1]).read()
for m in re.finditer(r'PROFILE-BEGIN (\S+) (\d+)\n(.*?)PROFILE-END', text, re.S):
    selfc, callers = parse(m.group(3))
    total = sum(selfc.values())
    share = defaultdict(float); alloc_by = defaultdict(float); alloc = 0
    for n, k in selfc.items():
        if n in ALLOC:
            alloc += k
            cs = {c: v for c, v in callers[n].items() if c not in ALLOC}
            tot = sum(cs.values()) or 1
            for c, v in cs.items(): alloc_by[cls(c)] += k * v / tot
        else:
            share[cls(n)] += k
    print(f'== {m.group(1)} n={m.group(2)}: {total} samples')
    print(f'  {100*alloc/total:5.1f}%  allocation (__bzero, memset), charged to:')
    for c, v in sorted(alloc_by.items(), key=lambda x: -x[1]):
        print(f'      {100*v/total:5.1f}%  {c}')
    print('  self time outside allocation:')
    for c, v in sorted(share.items(), key=lambda x: -x[1]):
        print(f'      {100*v/total:5.1f}%  {c}')
    print('  combined (allocation charged to its caller):')
    comb = defaultdict(float)
    for c, v in share.items(): comb[c] += v
    for c, v in alloc_by.items(): comb[c] += v
    for c, v in sorted(comb.items(), key=lambda x: -x[1]):
        print(f'      {100*v/total:5.1f}%  {c}')
