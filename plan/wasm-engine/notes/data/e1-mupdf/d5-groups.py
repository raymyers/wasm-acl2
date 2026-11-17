# E1 item 4 -> D5: group every instruction of an opcode census (census.sh
# output: "count mnemonic") into the engine's groups S0 to S3. Lines that are
# not instructions (wasm-objdump's "local[i..j]" declarations, words from
# the nix shell banner) are dropped. Usage: python3 -I d5-groups.py CENSUS
import sys, re
S0_CTRL = {'unreachable','nop','block','loop','if','else','end','br','br_if','br_table',
           'return','call','drop','select','local.get','local.set','local.tee',
           'global.get','global.set','memory.size','memory.grow','i32.const','i64.const'}
S1_CTRL = {'call_indirect','f32.const','f64.const'}
S2 = {'memory.copy','memory.fill','i32.extend8_s','i32.extend16_s','i64.extend8_s',
      'i64.extend16_s','i64.extend32_s'}
S3 = {'try_table','throw','throw_ref'}
INSTR = re.compile(r'^([a-z0-9_]+\.[a-z0-9_]+|[a-z_]+)$')
groups = {'S0': [], 'S1': [], 'S2': [], 'S3': [], 'other': []}
dropped = 0
for line in open(sys.argv[1]):
    parts = line.split()
    if len(parts) != 2 or not INSTR.match(parts[1]) or parts[1] in ('dev','all','top','proofs'):
        dropped += 1; continue
    n, op = int(parts[0]), parts[1]
    if op in S3: g = 'S3'
    elif op in S2: g = 'S2'
    elif op in S1_CTRL or op.startswith('f32.') or op.startswith('f64.') or 'f32' in op or 'f64' in op: g = 'S1'
    elif op in S0_CTRL or op.startswith('i32.') or op.startswith('i64.'): g = 'S0'
    else: g = 'other'
    groups[g].append((n, op))
for g, ops in groups.items():
    print(f'{g}: {len(ops)} instructions, {sum(n for n, _ in ops):,} occurrences')
    print('   ' + ' '.join(op for _, op in sorted(ops, key=lambda x: -x[0])))
print(f'(lines dropped as not instructions: {dropped})')
