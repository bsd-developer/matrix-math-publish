#!/usr/bin/env bash
set -euo pipefail
INFRA_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$INFRA_DIR"

SRC="${1:?usage: papers/build.sh <paper-directory>/<source.md>}"
SRC="$(cd "$(dirname "$SRC")" && pwd)/$(basename "$SRC")"
cd "$(dirname "$SRC")"
[ -f "$SRC" ] || { echo "no such file: $SRC" >&2; exit 1; }

OUT_BASENAME="$(basename "${SRC%.md}")"
OUT="build/${OUT_BASENAME}.pdf"
mkdir -p build

pandoc "$SRC" \
  --from markdown \
  --output "$OUT" \
  --pdf-engine=xelatex \
  --include-in-header="$INFRA_DIR/shared/preamble.tex" \
  --citeproc \
  --bibliography="$INFRA_DIR/shared/references.bib" \
  -V geometry:margin=0.88in \
  -V fontsize=10pt \
  -V colorlinks=true \
  --highlight-style=tango

# Strip identifying PDF metadata (author/creator/producer strings embedded
# by the toolchain); the release checklist requires an empty result here.
if command -v exiftool >/dev/null 2>&1; then
  exiftool -q -overwrite_original -all= "$OUT"
  echo "metadata after scrub:"
  exiftool "$OUT" | grep -iE "author|creator|producer" || echo "  (none)"
else
  echo "WARNING: exiftool not found; PDF metadata NOT scrubbed." >&2
  echo "Install it (brew install exiftool) and re-run before release." >&2
fi

echo "wrote $OUT"
