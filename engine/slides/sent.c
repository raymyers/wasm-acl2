/* A slide renderer for decks in the plain-text format of suckless sent
 * (https://tools.suckless.org/sent/), written for the verified engine
 * (plan/wasm-engine E12, milestone L0). It is not sent: it reads the same
 * format and draws in the same spirit, black on white, each slide scaled to
 * fit. It is our own code.
 *
 * The format: every paragraph (lines separated by an empty line) is a slide;
 * a line starting with '#' is a comment; a '\' at the start of a line
 * escapes a leading '@' or '#'. A paragraph '@FILE' is an image slide in
 * sent; here it is drawn as its text (there is no image decoder).
 *
 * Freestanding wasm32: no libc, no imports, integer arithmetic only. The deck
 * is a data segment (deck.h). render(n) draws slide n into a 1-bit
 * framebuffer of W x H pixels, row-major, 8 pixels per byte with the leftmost
 * in bit 7, 1 = black. A render clears the framebuffer a word at a time and
 * then draws glyph by glyph, a byte at a time: the cost follows the ink, not
 * the number of pixels. */

#include "font.h"   /* FONT[95][64][4], Spleen 32x64 */
#include "deck.h"   /* DECK[], DECK_LEN */

#define W 1280
#define H 720
#define ROWBYTES (W / 8)
#define GW 32       /* glyph width */
#define GH 64       /* glyph height */
#define GB (GW / 8) /* bytes in a glyph row */
#define MAXLINES 16
#define MARGIN_X 64
#define MARGIN_Y 36

static unsigned int fbw[ROWBYTES * H / 4];
#define fb ((unsigned char *)fbw)
static unsigned char rowbuf[ROWBYTES];     /* one glyph row, scaled */
static unsigned int line_start[MAXLINES];  /* offsets into DECK */
static unsigned int line_len[MAXLINES];

/* end of the line that starts at i */
static unsigned int line_end(unsigned int i) {
  while (i < DECK_LEN && DECK[i] != '\n') i++;
  return i;
}

/* Find slide n: fill line_start/line_len with its lines (comments dropped,
 * a leading backslash removed). Returns the number of lines, or -1 if there
 * is no slide n. */
static int find_slide(unsigned int n) {
  unsigned int i = 0, slide = 0;
  int in_par = 0, nl = 0;
  while (i < DECK_LEN) {
    unsigned int e = line_end(i);
    unsigned int len = e - i;
    if (len > 0 && DECK[i] == '#') {
      /* comment: ignored, does not end a paragraph */
    } else if (len == 0) {
      if (in_par) {
        if (slide == n) return nl;
        slide++;
        in_par = 0;
      }
    } else {
      in_par = 1;
      if (slide == n && nl < MAXLINES) {
        unsigned int s = i;
        if (DECK[s] == '\\') { s++; len--; }
        line_start[nl] = s;
        line_len[nl] = len;
        nl++;
      }
    }
    i = e + 1;
  }
  if (in_par && slide == n) return nl;
  return -1;
}

__attribute__((export_name("slide_count")))
int slide_count(void) {
  int n = 0;
  while (find_slide((unsigned int)n) >= 0) n++;
  return n;
}

__attribute__((export_name("framebuffer")))
int framebuffer(void) { return (int)(unsigned long)fb; }

__attribute__((export_name("width")))
int width(void) { return W; }

__attribute__((export_name("height")))
int height(void) { return H; }

/* Draw slide n. Returns the scale factor used, or -1 if there is no slide n. */
__attribute__((export_name("render")))
int render(int n) {
  int nl = find_slide((unsigned int)n);
  if (nl < 0) return -1;

  unsigned int maxlen = 1;
  for (int l = 0; l < nl; l++)
    if (line_len[l] > maxlen) maxlen = line_len[l];
  if (nl == 0) nl = 1, line_len[0] = 0;

  /* the largest integer scale at which the block fits inside the margins */
  unsigned int kx = (W - 2 * MARGIN_X) / (maxlen * GW);
  unsigned int ky = (H - 2 * MARGIN_Y) / ((unsigned int)nl * GH);
  unsigned int k = kx < ky ? kx : ky;
  if (k == 0) k = 1;

  unsigned int bw = maxlen * GW * k, bh = (unsigned int)nl * GH * k;
  unsigned int xb0 = bw < W ? (W - bw) / 16 : 0;  /* left edge, in bytes */
  unsigned int y0 = bh < H ? (H - bh) / 2 : 0;
  unsigned int cb = GB * k;                       /* bytes in a scaled glyph row */

  for (unsigned int i = 0; i < ROWBYTES * H / 4; i++) fbw[i] = 0;

  for (unsigned int l = 0; l < (unsigned int)nl; l++) {
    for (unsigned int c = 0; c < line_len[l]; c++) {
      unsigned int xb = xb0 + c * cb;
      if (xb + cb > ROWBYTES) break;              /* clipped on the right */
      unsigned int ch = (unsigned char)DECK[line_start[l] + c];
      if (ch < 32 || ch > 126) ch = '?';
      if (ch == ' ') continue;
      for (unsigned int gy = 0; gy < GH; gy++) {
        const unsigned char *g = FONT[ch - 32][gy];
        if (!(g[0] | g[1] | g[2] | g[3])) continue;
        unsigned int y = y0 + (l * GH + gy) * k;
        if (y + k > H) break;                     /* clipped at the bottom */
        unsigned char *dst = fb + y * ROWBYTES + xb;
        if (k == 1) {
          dst[0] = g[0]; dst[1] = g[1]; dst[2] = g[2]; dst[3] = g[3];
        } else {
          /* every glyph pixel becomes k pixels of rowbuf, then k rows */
          for (unsigned int i = 0; i < cb; i++) rowbuf[i] = 0;
          for (unsigned int sb = 0; sb < GB; sb++) {
            unsigned int v = g[sb];
            if (!v) continue;
            for (unsigned int bit = 0; bit < 8; bit++)
              if (v & (0x80u >> bit)) {
                unsigned int j = (sb * 8 + bit) * k, e = j + k;
                for (; j < e; j++) rowbuf[j >> 3] |= (unsigned char)(0x80u >> (j & 7));
              }
          }
          for (unsigned int r = 0; r < k; r++, dst += ROWBYTES)
            for (unsigned int i = 0; i < cb; i++) dst[i] = rowbuf[i];
        }
      }
    }
  }
  return (int)k;
}
