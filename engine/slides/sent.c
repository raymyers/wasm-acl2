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
 * in bit 7, 1 = black. Every framebuffer byte is written exactly once per
 * render, and a character and its glyph row are loaded only when they change:
 * memory accesses are the slow part on the engine's list machine (E0, E6). */

#include "font.h"   /* FONT[95][12], Spleen 6x12 */
#include "deck.h"   /* DECK[], DECK_LEN */

#define W 320
#define H 180
#define ROWBYTES (W / 8)
#define GW 6        /* glyph width */
#define GH 12       /* glyph height */
#define MAXLINES 16
#define MARGIN_X 16
#define MARGIN_Y 9

static unsigned char fb[ROWBYTES * H];
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
  unsigned int x0 = bw < W ? (W - bw) / 2 : 0;
  unsigned int y0 = bh < H ? (H - bh) / 2 : 0;

  unsigned int p = 0;  /* framebuffer index */
  for (unsigned int y = 0; y < H; y++) {
    int line = -1;
    unsigned int gy = 0, lstart = 0, llen = 0;
    if (y >= y0 && y < y0 + bh) {
      unsigned int ry = (y - y0) / k;
      line = (int)(ry / GH);
      gy = ry % GH;
      lstart = line_start[line];
      llen = line_len[line];
    }
    unsigned int cached_ci = 0xffffffffu, cached_row = 0;
    for (unsigned int bx = 0; bx < ROWBYTES; bx++) {
      unsigned int byte = 0;
      if (line >= 0) {
        for (unsigned int b = 0; b < 8; b++) {
          unsigned int x = bx * 8 + b;
          if (x >= x0) {
            unsigned int col = (x - x0) / k;
            unsigned int ci = col / GW;
            if (ci < llen) {
              if (ci != cached_ci) {
                unsigned int ch = (unsigned char)DECK[lstart + ci];
                if (ch < 32 || ch > 126) ch = '?';
                cached_row = FONT[ch - 32][gy];
                cached_ci = ci;
              }
              unsigned int gx = col % GW;
              if ((cached_row >> (7 - gx)) & 1u) byte |= 0x80u >> b;
            }
          }
        }
      }
      fb[p++] = (unsigned char)byte;
    }
  }
  return (int)k;
}
