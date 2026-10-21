#!/usr/bin/env bash
# Compile the research note using the repository's Markdown-TeX runtime.
set -euo pipefail
note_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
project_dir=$(cd "$note_dir/../.." && pwd)
build_dir=$(mktemp -d /tmp/pts-rk-consistency-note.XXXXXX)
printf 'Build directory: %s\n' "$build_dir"
ln -s "$note_dir/README.tex" "$build_dir/README.tex"
ln -s "$project_dir/latex/tex/development-preamble.tex" "$build_dir/development-preamble.tex"
for input in markdown.cls markdown.sty markdown; do
  ln -s "$project_dir/latex/$input" "$build_dir/$input"
done
cd "$build_dir"
latexmk -v > versions.log
lualatex --version >> versions.log
if latexmk -lualatex -interaction=nonstopmode -halt-on-error README.tex > build.log 2>&1; then
  printf '0\n' > build-exit-code.txt
else
  status=$?
  printf '%s\n' "$status" > build-exit-code.txt
  tail -60 build.log
  exit "$status"
fi
if rg 'LaTeX Warning: (Reference|There were undefined)|Missing character:|Overfull \\[hv]box' README.log; then
  printf 'Validation failed; existing PDF retained.\n' >&2
  exit 1
else
  status=$?
  if [[ "$status" != 1 ]]; then exit "$status"; fi
fi
cp README.pdf "$note_dir/README.pdf"
printf 'Build and validation exit code: 0\nPDF: %s\n' "$note_dir/README.pdf"
