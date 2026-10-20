#!/usr/bin/env bash
# Compile development expositions with the repository's Markdown-TeX runtime.
# Keep all intermediate files outside the checkout and publish only checked PDFs.
set -euo pipefail
project_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
for required_tool in latexmk lualatex rg; do
  if ! command -v "$required_tool" > /dev/null; then
    printf 'Missing required tool: %s\n' "$required_tool" >&2
    exit 127
  fi
done
build_dir=$(mktemp -d /tmp/pts-rk-development-docs.XXXXXX)
printf 'Build directory: %s\n' "$build_dir"
latexmk -v > "$build_dir/versions.log"
lualatex --version >> "$build_dir/versions.log"

documents=(
  theories/Interpretation_of_R
  theories/Interpretation_of_R/relational
  theories/Interpretation_of_R/functional
  theories/NormalizationComplexity
  docs/developments/ZFC_model
)

for document in "${documents[@]}"; do
  target="$build_dir/$document"
  mkdir -p "$target"
  ln -s "$project_dir/$document/README.tex" "$target/README.tex"
  ln -s "$project_dir/latex/tex/development-preamble.tex" "$target/development-preamble.tex"
  for input in markdown.cls markdown.sty markdown; do
    ln -s "$project_dir/latex/$input" "$target/$input"
  done
  printf 'Building %s\n' "$document"
  if (cd "$target" && latexmk -lualatex -interaction=nonstopmode \
      -halt-on-error README.tex > build.log 2>&1); then
    printf '0\n' > "$target/build-exit-code.txt"
  else
    status=$?
    printf '%s\n' "$status" > "$target/build-exit-code.txt"
    tail -60 "$target/build.log"
    printf 'Build failed (%s); existing PDFs retained. Log: %s\n' \
      "$status" "$target/build.log" >&2
    exit "$status"
  fi
  validation_status=0
  rg 'LaTeX Warning: (Reference|There were undefined)|Missing character:|Overfull \\[hv]box' \
      "$target/README.log" || validation_status=$?
  if [[ "$validation_status" == 0 ]]; then
    printf '1\n' > "$target/validation-exit-code.txt"
    printf 'Unresolved reference, missing glyph, or overflowing text; existing PDFs retained.\n' >&2
    exit 1
  elif [[ "$validation_status" != 1 ]]; then
    printf '%s\n' "$validation_status" > "$target/validation-exit-code.txt"
    printf 'Log validation failed (%s); existing PDFs retained.\n' "$validation_status" >&2
    exit "$validation_status"
  fi
  printf '0\n' > "$target/validation-exit-code.txt"
done

# A failed build above never partially refreshes the checked-in collection.
for document in "${documents[@]}"; do
  cp "$build_dir/$document/README.pdf" "$project_dir/$document/README.pdf"
  printf 'PDF: %s\n' "$project_dir/$document/README.pdf"
done
printf 'All development PDFs built successfully. Logs: %s\n' "$build_dir"
