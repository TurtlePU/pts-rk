#!/usr/bin/env bash
# Compile existing PTS-rk source, not a different PTS or an external model.
# Invoke from the repository root through: opam exec -- bash tools/ci-check-direct-r.sh
# This driver deliberately fails on the first unsuccessful stage. It does not
# turn admitted/unproved statements into theorems and is not a proof-completion test.
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"
[[ -f theories/DirectRCheck.v && -f theories/DirectRTests.v ]] || {
  echo 'Install the restructured DirectR package before running this workflow.' >&2
  exit 2
}
for tool in dune rocq opam git tar timeout; do
  command -v "$tool" >/dev/null || { echo "Missing runner tool: $tool" >&2; exit 127; }
done
BASELINE_REF="${DIRECT_R_BASELINE_REF:-723cf2ec61c737ae82ba33d2e7db44f650122b0e}"
JOBS="${DIRECT_R_JOBS:-2}"
SECONDS_PER_STAGE="${DIRECT_R_STAGE_SECONDS:-1200}"
[[ "$JOBS" =~ ^[1-9][0-9]*$ && "$SECONDS_PER_STAGE" =~ ^[1-9][0-9]*$ ]] || {
  echo 'DIRECT_R_JOBS and DIRECT_R_STAGE_SECONDS must be positive integers.' >&2
  exit 2
}
LOG_DIR="${DIRECT_R_LOG_DIR:-$(mktemp -d "${TMPDIR:-/tmp}/direct-r-ci-logs.XXXXXX")}"
mkdir -p "$LOG_DIR"
LOG_DIR="$(cd "$LOG_DIR" && pwd)"
BASELINE_DIR=''
CURRENT_STAGE='toolchain-inventory'
INTERRUPTED_BY=''
: > "$LOG_DIR/stages.tsv"
printf 'Stage\tResult\tExit code\n' > "$LOG_DIR/stages.tsv"
printf 'Diagnostic directory: %s\n' "$LOG_DIR"

finish() {
  local status=$?
  trap - EXIT
  set +e
  [[ ! -f "$ROOT/_build/log" ]] || cp "$ROOT/_build/log" "$LOG_DIR/direct-r-dune.log"
  if [[ -n "$BASELINE_DIR" && -f "$BASELINE_DIR/_build/log" ]]; then
    cp "$BASELINE_DIR/_build/log" "$LOG_DIR/upstream-dune.log"
  fi
  {
    printf 'Exit code: %s\nLast stage: %s\n' "$status" "$CURRENT_STAGE"
    if [[ -n "$INTERRUPTED_BY" ]]; then
      printf 'Interrupted by signal: %s\n' "$INTERRUPTED_BY"
    elif [[ "$status" -eq 143 || "$status" -eq 137 ]]; then
      printf 'A process was terminated by a signal; inspect the runner log.\n'
    elif [[ "$status" -eq 124 ]]; then
      printf 'The stage resource limit expired; this is not a compiler diagnostic.\n'
    fi
    printf '\nGreen means the supplied files compiled. It does NOT assert the missing\n'
    printf 'uniform GeneratorTotal/GeneratorSound or first-order soundness theorems.\n'
  } > "$LOG_DIR/result.txt"
  if [[ -n "${GITHUB_STEP_SUMMARY:-}" ]]; then
    {
      printf '## DirectR compiler run\n\n'
      printf '| Stage | Result | Exit code |\n|---|---|---|\n'
      tail -n +2 "$LOG_DIR/stages.tsv" | while IFS=$'\t' read -r stage result code; do
        printf '| %s | %s | %s |\n' "$stage" "$result" "$code"
      done
      printf '\nDriver exit code: `%s`. Last stage: `%s`.\n' "$status" "$CURRENT_STAGE"
      printf '\nA failed stage stops the sequence; later modules were not checked.\n'
      printf '\nDownload the **direct-r-logs** artifact for complete logs and toolchain versions.\n'
      printf '\n**Theorem 5 remains unfinished even if these builds succeed.**\n'
    } >> "$GITHUB_STEP_SUMMARY"
  fi
  # Do not erase the real failing code, even when log copying fails.
  exit "$status"
}
trap finish EXIT
# Preserve interruption evidence when the runner cancels the shell. SIGKILL or
# loss of the host cannot be trapped, and artifact upload is then not guaranteed.
interrupted() {
  INTERRUPTED_BY="$1"
  printf '%s\tINTERRUPTED\t%s\n' "$CURRENT_STAGE" "$2" >> "$LOG_DIR/stages.tsv"
  exit "$2"
}
trap 'interrupted TERM 143' TERM
trap 'interrupted INT 130' INT

{
  git rev-parse HEAD
  dune --version
  rocq -v
  ocamlc -version
  opam --version
  opam list --installed --columns=name,version
} 2>&1 | tee "$LOG_DIR/versions.log"
opam switch export "$LOG_DIR/opam-switch.export" \
  2>&1 | tee "$LOG_DIR/opam-switch-export.log"

stage() {
  local label="$1" work="$2"
  shift 2
  local command_status log_status
  local -a pipeline_status
  CURRENT_STAGE="$label"
  printf '\n=== %s ===\n' "$label"
  # The timeout is a diagnostic resource limit, not a proof of divergence.
  set +e
  (
    cd "$work"
    timeout --signal=TERM --kill-after=30s "$SECONDS_PER_STAGE" \
      dune build --display=short --no-buffer -j "$JOBS" "$@"
  ) 2>&1 | tee "$LOG_DIR/$label.log"
  pipeline_status=("${PIPESTATUS[@]}")
  set -e
  command_status="${pipeline_status[0]}"
  log_status="${pipeline_status[1]}"
  if [[ "$command_status" -eq 0 && "$log_status" -eq 0 ]]; then
    printf '%s\tPASS\t0\n' "$label" >> "$LOG_DIR/stages.tsv"
  else
    [[ "$command_status" -ne 0 ]] || command_status="$log_status"
    printf '%s\tFAIL\t%s\n' "$label" "$command_status" >> "$LOG_DIR/stages.tsv"
    printf '::error title=DirectR stage failed::%s failed (exit %s). See the diagnostic artifact.\n' \
      "$label" "$command_status"
    exit "$command_status"
  fi
}

# Build the ACTUAL unmodified upstream snapshot in a separate directory.
# A target in the patched working tree would not be an isolated baseline.
CURRENT_STAGE='prepare-pristine-upstream'
git cat-file -e "${BASELINE_REF}^{commit}"
BASELINE_DIR="$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/direct-r-upstream.XXXXXX")"
git archive "$BASELINE_REF" | tar -x -C "$BASELINE_DIR"
printf '%s\n' "$BASELINE_REF" > "$LOG_DIR/upstream-commit.txt"
stage 01-upstream "$BASELINE_DIR" theories/Ranks.vo

stage 02-kernel "$ROOT" theories/DirectRKernel.vo
stage 03-evaluator "$ROOT" theories/DirectREval.vo
stage 04-checker "$ROOT" theories/DirectRCheck.vo
stage 05-codes "$ROOT" theories/DirectRCodes.vo
stage 06-symbolic "$ROOT" theories/DirectRSymbolic.vo
stage 06a-structural "$ROOT" theories/DirectRStructural.vo
stage 06a-negative-logic "$ROOT" theories/DirectRLogic.vo
stage 06a-finite-tables "$ROOT" theories/DirectRFiniteTables.vo
stage 06a-positive-telescopes "$ROOT" theories/DirectRPositive.vo
stage 06a-finite-observations "$ROOT" theories/DirectRFiniteObservations.vo
stage 06b-foundations "$ROOT" theories/DirectRFoundations.vo
stage 06c-unary "$ROOT" theories/DirectRUnary.vo
stage 06c-finite-up "$ROOT" theories/DirectRFiniteUp.vo
stage 06c-unary-evaluation "$ROOT" theories/DirectRUnaryEvaluation.vo
stage 06c-separation "$ROOT" theories/DirectRSeparation.vo
stage 06c-unary-axioms "$ROOT" theories/DirectRUnaryAxioms.vo
stage 06c-unary-bounded "$ROOT" theories/DirectRUnaryBounded.vo
stage 06c-unary-arithmetic "$ROOT" theories/DirectRUnaryArithmetic.vo
stage 06c-unary-assumptions "$ROOT" theories/DirectRUnaryAudit.vo
stage 06c-relational-syntax "$ROOT" theories/DirectRRelationalSyntax.vo
stage 06c-relational-translation "$ROOT" theories/DirectRRelationalTranslation.vo
stage 06c-relational-equality "$ROOT" theories/DirectRRelationalEquality.vo
stage 06c-relational-deduction "$ROOT" theories/DirectRRelationalDeduction.vo
stage 06c-relational-countermodel "$ROOT" theories/DirectRRelationalCountermodel.vo
stage 06c-relational-ground "$ROOT" theories/DirectRRelationalGround.vo
stage 06c-relational-axioms "$ROOT" theories/DirectRRelationalAxioms.vo
stage 06c-theorem4 "$ROOT" theories/DirectRTheorem4.vo
stage 06c-relational-audit "$ROOT" theories/DirectRRelationalAudit.vo
stage 06d-source-countermodel "$ROOT" theories/DirectRCountermodel.vo
stage 06e-set-functions "$ROOT" models/SetFunctions.vo
stage 07-proof-families "$ROOT" theories/DirectRProofs.vo
stage 08-generators "$ROOT" theories/DirectRGenerated.vo
stage 09-first-order "$ROOT" theories/DirectRFirstOrder.vo
stage 10-obligations "$ROOT" theories/DirectRObligations.vo
stage 11-entry-point "$ROOT" theories/DirectR.vo
stage 12-arithmetic "$ROOT" theories/DirectRArithmetic.vo
# On a fresh checkout this compilation also emits the file's Print Assumptions.
stage 13-examples-and-assumptions "$ROOT" theories/DirectRTests.vo
CURRENT_STAGE='complete'
printf '\nAll requested builds passed; inspect the assumption report.\n'
printf 'The open Theorem 5 contracts have not thereby been discharged.\n'
