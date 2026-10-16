#!/usr/bin/env bash
# Compile the MLTT-S-style paper in an isolated directory, retaining its log.
set -euo pipefail

project_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
paper_dir="$project_dir/latex"
build_dir=$(mktemp -d /tmp/pts-rk-markdown-paper.XXXXXX)
printf 'Build directory: %s\n' "$build_dir"

for input in paper-markdown.tex tex markdown.cls markdown.sty markdown \
    verified-badges.sty badges bibliography.bib; do
  ln -s "$paper_dir/$input" "$build_dir/$input"
done

cd "$build_dir"
if latexmk -lualatex -interaction=nonstopmode -halt-on-error \
    -outdir="$build_dir" -auxdir="$build_dir" paper-markdown.tex \
    > "$build_dir/build.log" 2>&1; then
  if ! python3 "$project_dir/tools/check-markdown-paper.py" \
      --rendered-dir "$build_dir/_markdown_paper-markdown" \
      > "$build_dir/content-check.log" 2>&1; then
    cat "$build_dir/content-check.log"
    printf 'Content check failed; previous PDF retained.\n' >&2
    exit 1
  fi
  cat "$build_dir/content-check.log"
  cp "$build_dir/paper-markdown.pdf" "$paper_dir/paper-markdown.pdf"
  printf 'PDF: %s\nLog: %s\n' "$paper_dir/paper-markdown.pdf" "$build_dir/build.log"
else
  tail -60 "$build_dir/build.log"
  printf 'Build failed. Full log: %s\n' "$build_dir/build.log" >&2
  exit 1
fi
