#!/usr/bin/env bash
# Isolated functional-note build, sharing the bundled relational-note runtime.
set -euo pipefail

doc_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
note_dir=$(cd "$doc_dir/.." && pwd)
shared_doc=$(cd "$note_dir/../OrderedSemiring/doc" && pwd)
source_file="$note_dir/README.md"
publish_pdf=true
case "${1:-}" in
  "") ;;
  --smoke) source_file="$doc_dir/smoke.md"; publish_pdf=false ;;
  *) printf 'Usage: bash doc/build.sh [--smoke]\n' >&2; exit 2 ;;
esac
if [[ $# -gt 1 ]]; then
  printf 'Usage: bash doc/build.sh [--smoke]\n' >&2
  exit 2
fi
for program in lualatex texlua kpsewhich shasum; do
  command -v "$program" >/dev/null || {
    printf 'Required program not found: %s\n' "$program" >&2
    exit 1
  }
done

# Failed builds remain available; never overwrite the previous published PDF.
build_dir=$(mktemp -d /tmp/pts-rk-functional-note.XXXXXX)
printf 'Build directory: %s\n' "$build_dir"
finish() {
  result=$?
  printf '%s\n' "$result" > "$build_dir/exit-code.txt"
  if [[ "$result" -ne 0 ]]; then
    [[ ! -f "$build_dir/build.log" ]] || tail -n 60 "$build_dir/build.log" >&2
    printf 'Build failed; the previous README.pdf is unchanged.\n' >&2
  fi
  printf 'Logs and exact input snapshot: %s\n' "$build_dir"
}
trap finish EXIT

(cd "$shared_doc/runtime" && shasum -a 256 -c SHA256SUMS) \
  > "$build_dir/runtime-check.log" 2>&1
if [[ $(head -n 1 "$shared_doc/preamble.tex") != '\documentclass[11pt,a4paper]{article}' ]]; then
  printf 'Shared preamble class changed; update the functional wrapper explicitly.\n' >&2
  exit 1
fi
mkdir "$build_dir/doc"
cp "$source_file" "$build_dir/README.md"
cp "$doc_dir/preamble.tex" "$build_dir/doc/preamble.tex"
tail -n +2 "$shared_doc/preamble.tex" > "$build_dir/doc/shared-preamble.tex"
cp "$doc_dir/build.sh" "$shared_doc/check-rendered.lua" "$build_dir/doc/"
cp "$shared_doc/runtime/markdown.cls" "$shared_doc/runtime/markdown.sty" "$build_dir/"
cp -R "$shared_doc/runtime/markdown" "$build_dir/markdown"
cp "$shared_doc/runtime/SHA256SUMS" "$build_dir/SHA256SUMS"

cd "$build_dir"
lualatex --version > versions.log
kpsewhich --version >> versions.log
shasum -a 256 README.md doc/preamble.tex doc/shared-preamble.tex > input-sha256.log
printf 'TEXINPUTS=%q\n' "$build_dir//:" > environment.log
printf '%s\n' 'lualatex -no-shell-escape -interaction=nonstopmode -halt-on-error -file-line-error -recorder README.md' \
  > command.log
for pass in 1 2 3; do
  printf '\nLuaLaTeX pass %s\n' "$pass" >> build.log
  TEXINPUTS="$build_dir//:" lualatex -no-shell-escape -interaction=nonstopmode -halt-on-error \
    -file-line-error -recorder README.md >> build.log 2>&1
done
texlua doc/check-rendered.lua _markdown_README > rendered-check.log 2>&1
if grep -E 'Missing character:|There were undefined references|Reference .* undefined|Citation .* undefined|multiply defined|Rerun to get cross-references right' README.log \
    > diagnostics.log; then
  printf 'Unresolved references or missing glyphs; inspect diagnostics.log.\n' >&2
  exit 1
fi
if grep -E '/minted([./-]|$)|/minted\.sty|/latexminted' README.fls > unexpected-highlighter.log; then
  printf 'Unexpected minted dependency; inspect unexpected-highlighter.log.\n' >&2
  exit 1
fi
test -s README.pdf
if [[ "$publish_pdf" == true ]]; then
  cp README.pdf "$note_dir/README.pdf"
  printf 'PDF: %s\n' "$note_dir/README.pdf"
else
  printf 'Smoke PDF: %s/README.pdf\n' "$build_dir"
fi
