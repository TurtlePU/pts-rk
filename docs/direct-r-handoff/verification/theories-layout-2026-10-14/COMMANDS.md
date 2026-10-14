# Theories-layout verification — 2026-10-14

The pre-move baseline used c91f9564856a2a94afb7e2d55432693ae2d92bf0.
The existing BZC audit documentation was committed separately as
b4fb83b54e927276cbe2a0d8dc33429194cde931. The following tests check that
parent plus the uncommitted layout/build/documentation changes. All 169 moved
proof sources, the original kernel, and vendored sources remain unchanged.

## Environment

Commands run at the repository root on macOS using the existing local switch:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

OCaml 4.14.2, Dune 3.23.1, Rocq core 9.2.0, Stdlib 9.1.0,
Equations 1.3.2+9.2. Full resolved versions are retained alongside these logs.

## Before the move

```sh
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/theories-layout-baseline" bash tools/check-local-ci.sh > /tmp/pts-rk-theories-layout-baseline.log 2>&1
```

Exit 0: actionlint and all 171 stages passed, including an isolated pristine
upstream build. See baseline.log, baseline-stages.tsv, baseline-versions.log.
Working-tree modules could be cached; this is not the fresh build below.
Old status text in this baseline log is preserved verbatim.

## Fresh complete build and aliases

A new absolute build directory was allocated with
`mktemp -d /tmp/pts-rk-theories-layout-fresh.XXXXXX`, returning
`/tmp/pts-rk-theories-layout-fresh.ifuGK9`.

```sh
opam exec --switch=pts-rk-ci -- timeout 1200 dune build --build-dir '/tmp/pts-rk-theories-layout-fresh.ifuGK9' --display=short --no-buffer -j 2 @all > /tmp/pts-rk-theories-layout-fresh.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir '/tmp/pts-rk-theories-layout-fresh.ifuGK9' --display=short --no-buffer -j 2 @theories/Interpretation_of_R/relational/audit @theories/Interpretation_of_R/functional/audit @theories/ZFC_model/audit @theories/NormalizationComplexity/audit > /tmp/pts-rk-theories-layout-aliases.log 2>&1
```

Both exited 0. fresh.log is the newly executed full compiler output
(1257 closed source-level assumption reports); aliases.log is empty because
its dependencies were already compiled by that fresh build.
Nested-library loadpath remapping, existing notation, and large-nat warnings
are retained, not suppressed.

## Public types and transitive assumptions

The exact physical/logical mappings used after the move were:

```text
-Q '/tmp/pts-rk-theories-layout-fresh.ifuGK9/default/vendor/zfc' ZFC -Q '/tmp/pts-rk-theories-layout-fresh.ifuGK9/default/theories' PTSrk -Q '/tmp/pts-rk-theories-layout-fresh.ifuGK9/default/theories/Interpretation_of_R' Interpretation_of_R -Q '/tmp/pts-rk-theories-layout-fresh.ifuGK9/default/theories/Interpretation_of_R/relational' Interpretation_of_R.relational -Q '/tmp/pts-rk-theories-layout-fresh.ifuGK9/default/theories/Interpretation_of_R/functional' Interpretation_of_R.functional -Q '/tmp/pts-rk-theories-layout-fresh.ifuGK9/default/theories/NormalizationComplexity' PTSrk.NormalizationComplexity -Q '/tmp/pts-rk-theories-layout-fresh.ifuGK9/default/theories/ZFC_model' PTSrkModel
```

First audit invocation used these mappings but requested output basename
PUBLIC_AUDIT.vo for source AUDIT.v. Rocq rejected that CLI combination,
exit 1: source and target basenames must coincide. No theorem was compiled
in that failed invocation; its output is retained in types-failed.log.
Only the output basename was corrected:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 rocq c -Q '/tmp/pts-rk-theories-layout-fresh.ifuGK9/default/vendor/zfc' ZFC -Q '/tmp/pts-rk-theories-layout-fresh.ifuGK9/default/theories' PTSrk -Q '/tmp/pts-rk-theories-layout-fresh.ifuGK9/default/theories/Interpretation_of_R' Interpretation_of_R -Q '/tmp/pts-rk-theories-layout-fresh.ifuGK9/default/theories/Interpretation_of_R/relational' Interpretation_of_R.relational -Q '/tmp/pts-rk-theories-layout-fresh.ifuGK9/default/theories/Interpretation_of_R/functional' Interpretation_of_R.functional -Q '/tmp/pts-rk-theories-layout-fresh.ifuGK9/default/theories/NormalizationComplexity' PTSrk.NormalizationComplexity -Q '/tmp/pts-rk-theories-layout-fresh.ifuGK9/default/theories/ZFC_model' PTSrkModel -o '/tmp/pts-rk-theories-layout-fresh.ifuGK9/AUDIT.vo' docs/direct-r-handoff/verification/theories-layout-2026-10-14/AUDIT.v > /tmp/pts-rk-theories-layout-types.log 2>&1
```

Exit 0. types.log contains full types and 12 closed Print Assumptions reports
for Theorem 4, Theorem 7, effective Theorem5Target/deduction, original semantic
conversion/soundness/membership/model existence, the three normalization
bounds, and the Church-STLC reduction. Explicit model parameters remain
visible. This does not establish the material BZC foundation reduction or
formalize the external STLC hardness theorem.

## Recursive kernel checks

No dependency-admission options were used:

```sh
opam exec --switch=pts-rk-ci -- timeout 600 rocq check -silent -o -Q '/tmp/pts-rk-theories-layout-fresh.ifuGK9/default/vendor/zfc' ZFC -Q '/tmp/pts-rk-theories-layout-fresh.ifuGK9/default/theories' PTSrk -Q '/tmp/pts-rk-theories-layout-fresh.ifuGK9/default/theories/Interpretation_of_R' Interpretation_of_R -Q '/tmp/pts-rk-theories-layout-fresh.ifuGK9/default/theories/Interpretation_of_R/relational' Interpretation_of_R.relational -Q '/tmp/pts-rk-theories-layout-fresh.ifuGK9/default/theories/Interpretation_of_R/functional' Interpretation_of_R.functional -Q '/tmp/pts-rk-theories-layout-fresh.ifuGK9/default/theories/NormalizationComplexity' PTSrk.NormalizationComplexity -Q '/tmp/pts-rk-theories-layout-fresh.ifuGK9/default/theories/ZFC_model' PTSrkModel Interpretation_of_R.relational.DirectRTheorem4 Interpretation_of_R.functional.DirectRTheorem7 PTSrkModel.ModelSoundness PTSrk.NormalizationComplexity.Normalization PTSrk.NormalizationComplexity.STLCEmbedding > /tmp/pts-rk-theories-layout-kernel.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q '/tmp/pts-rk-theories-layout-fresh.ifuGK9/default/theories' PTSrk PTSrk.Ranks > /tmp/pts-rk-theories-layout-core-kernel.log 2>&1
```

Both exited 0. kernel.log and core-kernel.log have the same dependency-context
axiom, Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep.
Both report no type-in-type dependencies, unsafe (co)fixpoints, or assumed
positivity. This context-level upstream dependency is distinct from the
12 closed public theorem assumption reports.

## Source integrity, workflow syntax, and documentation links

```sh
layout_source_count=0
while IFS= read -r layout_source; do
  git show "HEAD:$layout_source" | cmp - "theories/$layout_source"
  layout_source_count=$((layout_source_count + 1))
done < <(git ls-tree -r --name-only HEAD Interpretation_of_R ZFC_model | rg '\.v$')
printf 'Unchanged moved proof sources: %s\n' "$layout_source_count"
git diff --exit-code HEAD -- theories/Syntax.v theories/AbstractRewriting.v theories/Congruence.v theories/Reduction.v theories/Confluence.v theories/DefEq.v theories/Context.v theories/Typing.v theories/Inversions.v theories/Preservation.v theories/SN.v theories/Ranks.v theories/dune vendor/zfc
bash -n tools/check-direct-r.sh tools/ci-check-direct-r.sh tools/check-local-ci.sh
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
actionlint .github/workflows/direct-r.yml
ruby -ruri -e 'bad = []; checked = 0; ARGV.each do |file|; File.read(file).scan(/\[[^\]]*\]\(([^)]+)\)/).each do |match|; link = match.first; next if link.match?(/\A(?:[a-z]+:|#)/i); target = URI::DEFAULT_PARSER.unescape(link.split("#", 2).first); checked += 1; bad << "#{file}: #{target}" unless File.exist?(File.expand_path(target, File.dirname(file))); end; end; puts "Checked #{checked} relative Markdown links"; abort(bad.join("\n")) unless bad.empty?' README.md theories/README.md theories/Interpretation_of_R/README.md theories/Interpretation_of_R/relational/README.md theories/Interpretation_of_R/functional/README.md theories/ZFC_model/README.md theories/NormalizationComplexity/README.md docs/README.md docs/direct-r-handoff/README.md docs/direct-r-handoff/BUILD.md docs/DirectR.md docs/DirectR-CI.md tools/README.md latex/README.md vendor/README.md
```

Exit 0, checks.log. All 169 moved .v files are identical, the original
kernel/Dune and vendored dependency are unchanged, shell syntax and actionlint
pass, and all 81 relative Markdown links in current guides resolve.
The set-model Dune module list was also compared token-for-token: the same
91 modules, only layout formatting and an audit alias added.

## Complete post-move local CI

```sh
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/theories-layout-final" bash tools/check-local-ci.sh > /tmp/pts-rk-theories-layout-ci.log 2>&1
```

Exit 0: actionlint and all 171 stages passed, including a newly archived
pristine upstream build. Stage names and PASS/exit-code results are identical
to the pre-move baseline. ci.log, stages.tsv, result.txt, and versions.log
retain the completed result. No Ubuntu runner/setup/upload emulation or remote
CI success is claimed. There was no build timeout or compiler proof failure;
the corrected audit output-basename error above is retained explicitly.

The smaller updated runner was then exercised against the completed build:

```sh
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/theories-layout-smoke" opam exec --switch=pts-rk-ci -- timeout 180 bash tools/check-direct-r.sh > /tmp/pts-rk-theories-layout-smoke.log 2>&1
```

Exit 0, smoke.log (cached dependencies). Raw verification output is retained
verbatim, including compiler-generated trailing whitespace. Whitespace checks
on edited source/guidance exclude these raw evidence logs.
