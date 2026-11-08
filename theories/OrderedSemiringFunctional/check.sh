#!/usr/bin/env bash
# Audit both interpretations and their shared infrastructure in a fresh build.
# No installation, network access, or generated files in the checkout.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"
if ! command -v opam >/dev/null 2>&1; then
  local_toolchain="${ORDERED_SEMIRING_TOOLCHAIN:-$HOME/.local/share/pts-rk-ci}"
  export PATH="$local_toolchain/bin:$PATH"
  export OPAMROOT="$local_toolchain/opam"
  export OPAMSWITCH=pts-rk-ci
fi
command -v opam >/dev/null 2>&1 || {
  printf '%s\n' 'Activate a Rocq 9.2 / Equations 1.3.2+9.2 opam switch first.' >&2
  exit 1
}
if [[ -n "${ORDERED_FUNCTIONAL_LOG_DIR:-}" ]]; then
  mkdir -p "$ORDERED_FUNCTIONAL_LOG_DIR"
  evidence_dir="$(cd "$ORDERED_FUNCTIONAL_LOG_DIR" && pwd)"
else
  evidence_dir="$(mktemp -d "${TMPDIR:-/tmp}/ordered-functional-logs.XXXXXX")"
fi
build_dir="$(mktemp -d "${TMPDIR:-/tmp}/ordered-functional-build.XXXXXX")"
printf 'Logs: %s\nFresh build: %s\n' "$evidence_dir" "$build_dir"
printf '%s\n' "$build_dir" > "$evidence_dir/build-directory.txt"
{
  opam exec -- rocq --version
  opam exec -- dune --version
  opam exec -- ocamlc -version
  opam list --installed --columns=name,version rocq-core rocq-stdlib rocq-equations
} > "$evidence_dir/versions.log" 2>&1

build_args=(build "--build-dir=$build_dir"
  @theories/Interpretation_of_R/audit
  @theories/Interpretation_of_R/relational/audit
  @theories/OrderedSemiring/audit
  @theories/OrderedSemiringFunctional/audit)
printf 'opam exec -- dune' > "$evidence_dir/build-command.txt"
printf ' %q' "${build_args[@]}" >> "$evidence_dir/build-command.txt"
printf '\n' >> "$evidence_dir/build-command.txt"
set +e
opam exec -- dune "${build_args[@]}" > "$evidence_dir/build.log" 2>&1
build_status=$?
set -e
printf '%s\n' "$build_status" > "$evidence_dir/build-exit-code.txt"
tail -55 "$evidence_dir/build.log"
if [[ "$build_status" -ne 0 ]]; then
  exit "$build_status"
fi

check_args=(-silent
  -Q "$build_dir/default/theories" PTSrk
  -Q "$build_dir/default/theories/Interpretation_of_R" Interpretation_of_R
  -Q "$build_dir/default/theories/Interpretation_of_R/relational" Interpretation_of_R.relational
  -Q "$build_dir/default/theories/OrderedSemiring" OrderedSemiring
  -Q "$build_dir/default/theories/OrderedSemiringFunctional" OrderedSemiringFunctional
  PTSrk.Ranks OrderedSemiring.TheoremOrderedSemiring
  OrderedSemiringFunctional.TheoremFunctionalSemiring)
printf 'opam exec -- rocq check' > "$evidence_dir/kernel-check-command.txt"
printf ' %q' "${check_args[@]}" >> "$evidence_dir/kernel-check-command.txt"
printf '\n' >> "$evidence_dir/kernel-check-command.txt"
set +e
opam exec -- rocq check "${check_args[@]}" > "$evidence_dir/kernel-check.log" 2>&1
check_status=$?
set -e
printf '%s\n' "$check_status" > "$evidence_dir/kernel-check-exit-code.txt"
tail -20 "$evidence_dir/kernel-check.log"
printf 'Compilation exit: %s; recursive kernel-check exit: %s\n' "$build_status" "$check_status"
exit "$check_status"
