#!/usr/bin/env bash
# Invoked from a per-run read-only snapshot, never edited during execution.
set -euo pipefail
[[ "$#" -eq 4 ]] || { printf 'Use AUDIT.sh to launch an immutable run.\n' >&2; exit 2; }
HORN_ROOT="$1"
HORN_LOG="$2"
HORN_EVIDENCE="$3"
HORN_SNAPSHOT="$4"
cd "$HORN_ROOT"
source "$HORN_SNAPSHOT/SCOPE.sh"
[[ "$HORN_FROZEN" == yes ]] || exit 2
HORN_LOCAL="${XDG_DATA_HOME:-$HOME/.local/share}/pts-rk-ci"
export PATH="$HORN_LOCAL/bin:$PATH"
export OPAMROOT="$HORN_LOCAL/opam"
export OPAMSWITCH=pts-rk-ci
export PYTHONDONTWRITEBYTECODE=1
HORN_BASE=723cf2ec61c737ae82ba33d2e7db44f650122b0e
HORN_DIR=theories/self_consistency
HORN_BASELINE="$HORN_EVIDENCE/baseline"
HORN_BUILD="$(mktemp -d /tmp/pts-rk-uniform-horn-fresh.XXXXXX)"
HORN_PRISTINE="$(mktemp -d /tmp/pts-rk-uniform-horn-pristine.XXXXXX)"
HORN_ARCHIVE="$(mktemp -d "$HORN_EVIDENCE/audit.XXXXXX")"
HORN_SOURCES=("$HORN_DIR/$HORN_AUDIT.v")
for horn_module in "${HORN_MODULES[@]}"; do HORN_SOURCES+=("$HORN_DIR/$horn_module.v"); done
printf 'Logs: %s\nBuild: %s\nPristine: %s\nArchive: %s\nDriver: %s\n' \
  "$HORN_LOG" "$HORN_BUILD" "$HORN_PRISTINE" "$HORN_ARCHIVE" "$HORN_SNAPSHOT" | tee "$HORN_LOG/paths.txt"
printf 'stage\texit\tstart_utc\tend_utc\n' > "$HORN_LOG/status.tsv"

archive_logs() {
  local horn_file horn_target
  mkdir -p "$HORN_ARCHIVE/driver" || return "$?"
  cp "$HORN_SNAPSHOT"/* "$HORN_ARCHIVE/driver/" || return "$?"
  for horn_file in "$HORN_LOG"/*.log "$HORN_LOG"/*.txt "$HORN_LOG"/*.tsv "$HORN_LOG"/*.sha256; do
    [[ -f "$horn_file" ]] || continue
    horn_target="$HORN_ARCHIVE/$(basename "$horn_file")"
    gzip -c "$horn_file" > "$horn_target.raw.gz" || return "$?"
    cmp "$horn_file" <(gzip -dc "$horn_target.raw.gz") || return "$?"
    perl -0pe 's/[ \t]+$//mg; s/\n+\z/\n/' "$horn_file" > "$horn_target" || return "$?"
  done
}
finish() {
  local horn_result="$?" horn_archive_result=0
  trap - EXIT
  printf '%s\n' "$horn_result" > "$HORN_LOG/execution-result.txt"
  archive_logs || horn_archive_result="$?"
  if [[ "$horn_result" -eq 0 && "$horn_archive_result" -ne 0 ]]; then horn_result="$horn_archive_result"; fi
  printf '%s\n' "$horn_result" > "$HORN_LOG/result.txt"
  printf '%s\n' "$horn_archive_result" > "$HORN_LOG/archive-result.txt"
  if [[ "$horn_archive_result" -eq 0 ]]; then
    cp "$HORN_LOG/result.txt" "$HORN_LOG/archive-result.txt" "$HORN_ARCHIVE/" || horn_result="$?"
    printf '%s\n' "$horn_result" > "$HORN_LOG/result.txt"
  fi
  printf 'Final exit: %s; archive exit: %s; logs: %s\n' "$horn_result" "$horn_archive_result" "$HORN_LOG"
  exit "$horn_result"
}
trap finish EXIT
run() {
  local horn_label="$1" horn_started horn_finished horn_result
  shift
  horn_started="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%q ' "$@" >> "$HORN_LOG/commands.txt"
  printf '\n' >> "$HORN_LOG/commands.txt"
  set +e
  "$@" > "$HORN_LOG/$horn_label.log" 2>&1
  horn_result="$?"
  set -e
  horn_finished="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '%s\t%s\t%s\t%s\n' "$horn_label" "$horn_result" "$horn_started" "$horn_finished" | tee -a "$HORN_LOG/status.tsv"
  if [[ "$horn_result" -ne 0 ]]; then tail -70 "$HORN_LOG/$horn_label.log"; exit "$horn_result"; fi
}
source_manifest() {
  {
    awk '{print $2}' "$HORN_BASELINE/sources.sha256" || return "$?"
    printf '%s\n' "${HORN_SOURCES[@]}" || return "$?"
  } | LC_ALL=C sort -u | while IFS= read -r horn_source; do
    shasum -a 256 "$horn_source" || return "$?"
  done
}
previous_sources() {
  # Exactly two metadata files may change; every older proof remains frozen.
  awk '$2 != "theories/self_consistency/Audit.v" && $2 != "theories/self_consistency/dune"' \
    "$HORN_BASELINE/sources.sha256" > "$HORN_LOG/previous-sources.sha256" || return "$?"
  shasum -a 256 -c "$HORN_LOG/previous-sources.sha256"
}
registration() {
  python3 "$HORN_SNAPSHOT/gates.py" registration "$HORN_BASELINE" "$HORN_ROOT" \
    "$HORN_AUDIT" "$HORN_ALIAS" "${HORN_MODULES[@]}"
}
safety() {
  local horn_result
  if rg -n '\b(Admitted|admit|Axiom|Axioms|Parameter|Parameters|Conjecture|Conjectures)\b|Unset (Guard|Positivity|Universe) Checking|bypass_check' "${HORN_SOURCES[@]}"; then
    return 1
  else
    horn_result="$?"
    [[ "$horn_result" -eq 1 ]] || return "$horn_result"
  fi
}
whitespace() {
  local horn_source horn_diagnostic horn_result
  for horn_source in "${HORN_SOURCES[@]}" "$HORN_DIR/dune" "$HORN_DIR/Audit.v" \
      "$HORN_SNAPSHOT"/*.sh "$HORN_SNAPSHOT"/*.py; do
    [[ -f "$horn_source" ]] || return 1
    if horn_diagnostic="$(git diff --no-index --check /dev/null "$horn_source" 2>&1)"; then
      horn_result=0
    else
      horn_result="$?"
    fi
    if [[ "$horn_result" -gt 1 || -n "$horn_diagnostic" ]]; then
      printf '%s\n' "$horn_diagnostic"; return 1
    fi
  done
}

run driver-snapshot shasum -a 256 -c "$HORN_LOG/driver-before.sha256"
run head git rev-parse HEAD
run disk df -h . /private/tmp
run rocq-version opam exec -- rocq -v
run dune-version opam exec -- dune --version
run packages opam list --installed --columns=name,version
run gate-regressions python3 "$HORN_SNAPSHOT/GATE-TESTS.py"
run source-before source_manifest
run preceding-bodies previous_sources
run additive-registration registration
run public-coverage python3 "$HORN_SNAPSHOT/gates.py" declarations "$HORN_ROOT" "$HORN_AUDIT" "${HORN_MODULES[@]}"
run source-safety safety
run source-whitespace whitespace
run pristine-archive git archive --output="$HORN_LOG/pristine.tar" "$HORN_BASE"
run pristine-extract tar -xf "$HORN_LOG/pristine.tar" -C "$HORN_PRISTINE"
run pristine-build opam exec -- timeout 600 dune build --root "$HORN_PRISTINE" --display=short --no-buffer -j 2 theories/Ranks.vo
run pristine-kernel opam exec -- timeout 600 rocq check -silent -o -bytecode-compiler yes \
  -Q "$HORN_PRISTINE/_build/default/theories" PTSrk PTSrk.Ranks
run fresh-build opam exec -- timeout 3600 dune build --build-dir "$HORN_BUILD" --display=short --no-buffer -j 2 "@theories/self_consistency/$HORN_ALIAS"
run closure-reports python3 "$HORN_SNAPSHOT/gates.py" reports "$HORN_ROOT" "$HORN_BUILD" "$HORN_LOG/fresh-build.log"
run kernel opam exec -- timeout 3600 rocq check -silent -o -bytecode-compiler yes \
  -Q "$HORN_BUILD/default/theories" PTSrk \
  -Q "$HORN_BUILD/default/theories/NormalizationComplexity" PTSrk.NormalizationComplexity \
  -Q "$HORN_BUILD/default/theories/Interpretation_of_R" Interpretation_of_R \
  -Q "$HORN_BUILD/default/theories/CombinatoryLogic-rk" PTSrk.Combinatory \
  -Q "$HORN_BUILD/default/theories/self_consistency" PTSrk.SelfConsistency \
  "PTSrk.SelfConsistency.$HORN_AUDIT"
run pristine-inventory python3 "$HORN_SNAPSHOT/gates.py" inventory "$HORN_LOG/pristine-kernel.log" "$HORN_LOG/kernel.log"
run original-kernel git diff --exit-code "$HORN_BASE" -- \
  theories/Syntax.v theories/AbstractRewriting.v theories/Congruence.v \
  theories/Reduction.v theories/Confluence.v theories/DefEq.v theories/Context.v \
  theories/Typing.v theories/Inversions.v theories/Preservation.v theories/SN.v theories/Ranks.v
run frozen-zfc git diff --exit-code ffa7131 -- theories/ZFC_model
run source-after source_manifest
run source-stable cmp "$HORN_LOG/source-before.log" "$HORN_LOG/source-after.log"
run preceding-bodies-after previous_sources
run additive-registration-after registration
run driver-unchanged shasum -a 256 -c "$HORN_LOG/driver-before.sha256"
printf 'PASS: fresh uniform-Horn dependency closure and complete recursive kernel check.\n'
