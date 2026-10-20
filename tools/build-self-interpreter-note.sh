#!/usr/bin/env bash
# Build the research note using the repository's pinned Markdown-TeX dialect.
set -euo pipefail
project_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
build_dir=$(mktemp -d /tmp/pts-rk-self-note.XXXXXX)
printf 'Build directory: %s\n' "$build_dir"
ln -s "$project_dir/PTS-rk_self_interpreter.tex" "$build_dir/PTS-rk_self_interpreter.tex"
ln -s "$project_dir/latex/tex/self-interpreter-preamble.tex" "$build_dir/self-interpreter-preamble.tex"
for input in markdown.cls markdown.sty markdown; do
  ln -s "$project_dir/latex/$input" "$build_dir/$input"
done
cd "$build_dir"
latexmk -v > versions.log
lualatex --version >> versions.log
if latexmk -lualatex -interaction=nonstopmode -halt-on-error \
    PTS-rk_self_interpreter.tex > build.log 2>&1; then
  if rg 'LaTeX Warning: (Reference|There were undefined)|Missing character:' \
      PTS-rk_self_interpreter.log; then
    printf 'Unresolved reference or missing glyph; previous PDF retained.\n' >&2
    exit 1
  fi
  cp PTS-rk_self_interpreter.pdf "$project_dir/PTS-rk_self_interpreter.pdf"
  printf 'Build exit code: 0\nPDF: %s\nLog: %s\n' \
    "$project_dir/PTS-rk_self_interpreter.pdf" "$build_dir/build.log"
else
  status=$?
  tail -60 build.log
  printf 'Build exit code: %s\nLog: %s\n' "$status" "$build_dir/build.log" >&2
  exit "$status"
fi
