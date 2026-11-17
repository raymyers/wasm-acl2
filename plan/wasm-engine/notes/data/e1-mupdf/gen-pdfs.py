# E1 item 6: two more test PDFs, written byte for byte by this script (stdlib
# only, deterministic). Usage: python3 -I gen-pdfs.py OUTDIR  (here: OUTDIR = .)
#   slide.pdf  960 x 540 (16:9): a title, bullets, an axial shading, a Flate
#              RGB image, filled and stroked shapes. The slide of the plan.
#   text.pdf   612 x 792: several base-14 fonts, rotated and scaled text,
#              dashed and clipped paths, a CMYK fill and a gray fill.
import sys, zlib, os

def pdf(objs, path):
    # objs: list of bytes (object bodies), object 1 is the catalog
    out = bytearray(b"%PDF-1.7\n%\xe2\xe3\xcf\xd3\n")
    offs = []
    for i, body in enumerate(objs, 1):
        offs.append(len(out))
        out += b"%d 0 obj\n" % i + body + b"\nendobj\n"
    xref = len(out)
    out += b"xref\n0 %d\n0000000000 65535 f \n" % (len(objs) + 1)
    for o in offs:
        out += b"%010d 00000 n \n" % o
    out += b"trailer\n<< /Size %d /Root 1 0 R >>\nstartxref\n%d\n%%%%EOF\n" % (len(objs) + 1, xref)
    open(path, "wb").write(out)

def stream(dict_extra, data, flate=False):
    if flate:
        data = zlib.compress(data, 9)
        dict_extra += b" /Filter /FlateDecode"
    return b"<< /Length %d %s >>\nstream\n" % (len(data), dict_extra) + data + b"\nendstream"

def font(name):
    return b"<< /Type /Font /Subtype /Type1 /BaseFont /%s /Encoding /WinAnsiEncoding >>" % name

def slide(path):
    w, h = 64, 48
    img = bytearray()
    for y in range(h):
        for x in range(w):
            img += bytes(((x * 4) & 255, (y * 5) & 255, ((x ^ y) * 8) & 255))
    content = b"""
0.97 0.97 0.94 rg 0 0 960 540 re f
q /Sh1 sh Q
0.10 0.20 0.45 rg 0 460 960 80 re f
BT /F1 40 Tf 1 1 1 rg 48 485 Td (A verified WebAssembly engine) Tj ET
BT /F2 24 Tf 0.1 0.1 0.1 rg 60 390 Td 30 TL
(\\225 The generated semantics is the specification) Tj T*
(\\225 The engine is a second, faster definition) Tj T*
(\\225 ACL2 proves that the two agree) Tj T*
(\\225 MuPDF renders this slide) Tj ET
q 256 0 0 192 640 120 cm /Im1 Do Q
2 w 0.85 0.33 0.10 RG 640 120 256 192 re S
0.20 0.60 0.30 rg 60 60 m 160 60 l 110 140 l h f
0.1 0.1 0.1 RG 4 w 1 J 200 70 m 260 140 320 0 380 70 c S
BT /F3 14 Tf 0.4 0.4 0.4 rg 48 20 Td (wasm-acl2, plan/wasm-engine E1) Tj ET
"""
    # q /Sh1 sh Q without a clip fills the page; clip it to a band first
    content = content.replace(b"q /Sh1 sh Q", b"q 0 320 960 140 re W n /Sh1 sh Q")
    objs = [
        b"<< /Type /Catalog /Pages 2 0 R >>",
        b"<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
        b"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 960 540] /Contents 4 0 R "
        b"/Resources << /Font << /F1 5 0 R /F2 6 0 R /F3 7 0 R >> /XObject << /Im1 8 0 R >> "
        b"/Shading << /Sh1 9 0 R >> >> >>",
        stream(b"", content, flate=True),
        font(b"Helvetica-Bold"), font(b"Helvetica"), font(b"Times-Italic"),
        stream(b"/Type /XObject /Subtype /Image /Width %d /Height %d /ColorSpace /DeviceRGB /BitsPerComponent 8" % (w, h), bytes(img), flate=True),
        b"<< /ShadingType 2 /ColorSpace /DeviceRGB /Coords [0 0 960 0] /Extend [true true] "
        b"/Function << /FunctionType 2 /Domain [0 1] /C0 [0.85 0.90 1.0] /C1 [1.0 0.92 0.80] /N 1 >> >>",
    ]
    pdf(objs, path)

def text(path):
    content = b"""
BT /F1 28 Tf 72 720 Td (Times-Roman, 28 pt) Tj ET
BT /F2 18 Tf 72 680 Td (Courier: fixed width 0123456789) Tj ET
BT /F3 14 Tf 72 650 Td 18 TL
(Helvetica-Oblique: the quick brown fox jumps over the lazy dog.) Tj T*
(Second line, with kerning-free text and punctuation: ;:,.!?) Tj ET
BT /F4 12 Tf 0.866 0.5 -0.5 0.866 300 400 Tm (Rotated 30 degrees, Helvetica-Bold) Tj ET
BT /F1 10 Tf 2 0 0 1 72 300 Tm (Horizontally scaled Times) Tj ET
q 1 0 0 0 k 72 100 200 120 re f Q
q 0.5 g 320 100 200 120 re f Q
q 3 w [12 6] 0 d 0.8 0 0 RG 72 260 m 540 260 l S Q
q 400 500 m 500 600 l 560 480 l h W n 0 0 1 rg 380 460 200 160 re f Q
q 1 w 0 0.5 0 RG 420 560 60 0 360 re S Q
"""
    objs = [
        b"<< /Type /Catalog /Pages 2 0 R >>",
        b"<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
        b"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Contents 4 0 R "
        b"/Resources << /Font << /F1 5 0 R /F2 6 0 R /F3 7 0 R /F4 8 0 R >> >> >>",
        stream(b"", content),
        font(b"Times-Roman"), font(b"Courier"), font(b"Helvetica-Oblique"), font(b"Helvetica-Bold"),
    ]
    pdf(objs, path)

d = sys.argv[1]
slide(os.path.join(d, "slide.pdf"))
text(os.path.join(d, "text.pdf"))
