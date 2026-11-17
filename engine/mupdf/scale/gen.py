# E1 item 5: synthetic modules of growing size, to measure how the generated
# decoder's time grows with module size. N functions, each 64 instructions
# (local.get, i32.const, i32.add, i32.store/load, br_if in a block).
# Usage: python3 -I gen.py N > m-N.wat
import sys
n = int(sys.argv[1])
print('(module (memory 1)')
for i in range(n):
    body = ' '.join(['(local.set 0 (i32.add (local.get 0) (i32.const %d)))' % (j + i) for j in range(10)])
    print('  (func (param i32) (result i32) (block %s (i32.store (i32.const 0) (local.get 0)) (br_if 0 (i32.load (i32.const 0)))) (local.get 0))' % body)
print(')')
