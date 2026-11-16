#!/bin/sh
# E1 item 9: the second, smaller target. Everything a PDF of the talk does
# not need is off: every document type but PDF, the HTML engine, JavaScript,
# ICC colour management, JPEG 2000, barcodes, OCR and office output, and all
# fonts but the base-14 set (TOFU, TOFU_CJK, TOFU_EMOJI, TOFU_HISTORIC,
# TOFU_SYMBOL, TOFU_SIL). Output in WORKDIR/out-small/.
# Usage: sh engine/mupdf/build-small.sh WORKDIR [FORK_COMMIT]
D="-DTOFU -DTOFU_CJK -DTOFU_EMOJI -DTOFU_HISTORIC -DTOFU_SYMBOL -DTOFU_SIL -DFZ_ENABLE_HYPHEN=0"
D="$D -DFZ_ENABLE_XPS=0 -DFZ_ENABLE_SVG=0 -DFZ_ENABLE_CBZ=0 -DFZ_ENABLE_IMG=0 -DFZ_ENABLE_HTML=0"
D="$D -DFZ_ENABLE_MD=0 -DFZ_ENABLE_EPUB=0 -DFZ_ENABLE_FB2=0 -DFZ_ENABLE_MOBI=0 -DFZ_ENABLE_OFFICE=0"
D="$D -DFZ_ENABLE_TXT=0 -DFZ_ENABLE_HTML_ENGINE=0 -DFZ_ENABLE_OCR_OUTPUT=0 -DFZ_ENABLE_DOCX_OUTPUT=0"
D="$D -DFZ_ENABLE_ODT_OUTPUT=0 -DFZ_ENABLE_ICC=0 -DFZ_ENABLE_JPX=0 -DFZ_ENABLE_JS=0 -DFZ_ENABLE_BARCODE=0"
D="$D -DFZ_ENABLE_BROTLI=0"
DEFINES="$D" FEATURES="brotli=no mujs=no extract=no xps=no svg=no html=no tesseract=no barcode=no" \
  SUFFIX=-small exec sh "$(dirname "$0")/build.sh" "$@"
