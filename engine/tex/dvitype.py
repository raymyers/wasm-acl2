# A small DVI reader: prints the preamble, the fonts and the characters set
# on each page. Usage: python3 -I dvitype.py FILE.dvi
import sys
b = open(sys.argv[1], 'rb').read()
i = 0
def u(n):
    global i
    v = int.from_bytes(b[i:i+n], 'big'); i += n; return v
def s(n):
    global i
    v = int.from_bytes(b[i:i+n], 'big', signed=True); i += n; return v
fonts, text, page = {}, [], 0
while i < len(b):
    op = u(1)
    if op <= 127: text.append(chr(op))
    elif 128 <= op <= 131: text.append(chr(u(op - 127)))
    elif op == 132: u(8)
    elif 133 <= op <= 136: u(op - 132)
    elif op == 137: u(8)
    elif op == 138: pass
    elif op == 139:
        page += 1; cs = [s(4) for _ in range(10)]; s(4); text = []
        print('page', page, 'count0', cs[0])
    elif op == 140: print('  text:', ''.join(text)); text = []
    elif op in (141, 142): pass
    elif 143 <= op <= 146: s(op - 142); text.append(' ')
    elif op == 147: text.append(' ')
    elif 148 <= op <= 151: s(op - 147); text.append(' ')
    elif op == 152: pass
    elif 153 <= op <= 156: s(op - 152)
    elif 157 <= op <= 160: s(op - 156); text.append(' | ')
    elif op == 161: text.append(' | ')
    elif 162 <= op <= 165: s(op - 161); text.append(' | ')
    elif op == 166: pass
    elif 167 <= op <= 170: s(op - 166)
    elif 171 <= op <= 234: text.append('<f%d>' % (op - 171))
    elif 235 <= op <= 238: text.append('<f%d>' % u(op - 234))
    elif 239 <= op <= 242:
        n = u(op - 238); print('  special:', b[i:i+n].decode('latin1')); i += n
    elif 243 <= op <= 246:
        k = u(op - 242); u(4); sc = u(4); ds = u(4); a = u(1); l = u(1)
        name = b[i:i+a+l].decode('latin1'); i += a + l
        if k not in fonts: fonts[k] = name; print('  font', k, name, 'at %.2fpt' % (sc / 65536))
    elif op == 247:
        ver = u(1); num = u(4); den = u(4); mag = u(4); k = u(1)
        print('preamble: version', ver, 'mag', mag, 'comment', b[i:i+k].decode('latin1')); i += k
    elif op == 248:
        print('postamble at', i - 1); break
    else:
        print('unknown opcode', op, 'at', i - 1); break
