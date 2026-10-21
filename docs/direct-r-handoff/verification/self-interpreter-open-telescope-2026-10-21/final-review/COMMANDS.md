# Full dependent numerical-plan interpretation — final independent audit

Base commit `e822cd62df393faf4d5e4ed0c4c8fed173ccba6f`, 21 October 2026.
All proof sources, Dune and Audit were frozen before verification. This
reviewer does not mutate proof sources, Git or the index during the audit.
The parent owns the note/PDF and live handoff updates.

## Status

The complete unchanged local CI passed, exit 0, 06:32:52–06:39:14 UTC:
226/226 stages PASS, including pristine upstream and actionlint. Its
`staged/result.txt` says `Last stage: complete`. No stage failed or timed out.

The first separate fresh aggregate build exhausted disk space. Its complete
compile output and Dune trace were preserved; this was not a proof rejection.
After reclaiming completed regenerable caches, a new empty absolute build
directory was created and the full fresh audit restarted at 06:38:37 UTC.
That independent fresh audit passed, exit 0, 06:38:37–06:55:34 UTC, with
exactly 2230 closed reports: 2229 from self-interpreter sources and the
unchanged upstream `Ranks.strong_normalization` report. All 14 audit stages
passed. Both original-core and aggregate recursive kernel checks passed.
The aggregate loaded inventory contains only unchanged upstream
`Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`;
there is no type-in-type, unsafe fixpoint or assumed positivity. Original-core
inventory is byte-identical to both a new pristine upstream build and the
historical pristine inventory. No incomplete or cached assumption output is
counted as a final fresh report.

The frozen manifest contains 110 entries: 107 self-interpreter proof files
(including Audit), Dune and the two CI scripts. Audit contains 885 public
Check/Print pairs. The 2229 self-interpreter reports consist of those 885
aggregate reports and 1344 module reports. The initial expectation of 2229
total omitted the one upstream report; this is reconciled against the actual
source declarations, not an additional new assumption. Initial and retry
manifests are byte-identical.

Original kernel, NormalizationComplexity and frozen PR #1 ZFC comparisons
all passed against `ffa7131`. All 110 source/script hashes remained unchanged
across the complete fresh build/kernel audit. Safety scan and runner syntax
checks passed. `FINAL-CHECKS.sh` separately confirmed exact report/manifest/
Audit/CI counts, initial-versus-retry hashes, source/evidence whitespace,
unchanged HEAD and an empty staged diff, exit 0. Disk availability at completion
was about 652 MiB. No final retry stage failed or timed out.

Final public-source SHA256 checkpoints (the complete manifest is retained
with the raw run):

```text
e7320f3c45a1a6b3bf5deff9fb6d8e1cb34fc57718d1763ec3901442c491db6d  Audit.v
c55de89ec762064229071882dd8b6409b079da7d7f2d1d13135b6973f3c1aba9  dune
5fc3541041f88ebc02435e66acf40a86e1a42eeea2db1fe62b65038052ee33fa  FullDependentInterpreter.v
38559f389ca8c7e7d343ddd4f0dfa95eefa5b030b2b2d06ef13b1c8855afd2f2  RecursiveQuotation.v
```

## Exact runners and environment

Ignored local-only raw artifacts, not promised in a clean checkout:

- Initial attempt and successful complete CI:
  `_build/self-interpreter-open-telescope-final-review.d0SH8N/`.
  Scripts `AUDIT.sh`, `CI.sh`, `CLEAN-FAILED.sh`; outputs include
  `fresh-build.log`, `failed-trace.csexp`, `audit-driver.log`, `status.tsv`,
  `audit-exit-code.txt`, `ci-driver.log`, `ci-exit-code.txt`,
  `staged/stages.tsv`, `staged/result.txt`, versions and source hashes.
- Fully fresh retry:
  `_build/self-interpreter-open-telescope-final-review-retry.mfFz4Q/`.
  `AUDIT.sh` captures every command, exit code and stage log, versions,
  source manifests, assumption count and all comparisons. `FINAL-CHECKS.sh`,
  `final-checks.log` and `final-checks-exit-code.txt` record the independent
  closing assertions. Both drivers and closing assertions exited 0.

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
timeout 1200 opam exec -- dune build \
  --build-dir=/tmp/pts-rk-self-open-telescope-audit-retry.cdzdRH \
  --display=short --no-buffer -j 2 @theories/self_interpreter/audit
timeout 1200 opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-self-open-telescope-audit-retry.cdzdRH/default/theories PTSrk \
  PTSrk.Ranks
timeout 1200 opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-self-open-telescope-audit-retry.cdzdRH/default/theories PTSrk \
  -Q /tmp/pts-rk-self-open-telescope-audit-retry.cdzdRH/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-self-open-telescope-audit-retry.cdzdRH/default/theories/self_interpreter PTSrk.SelfInterpreter \
  PTSrk.SelfInterpreter.Audit

git archive 723cf2ec61c737ae82ba33d2e7db44f650122b0e |
  tar -x -C /tmp/pts-rk-self-open-telescope-pristine.oGwrNN
timeout 1200 opam exec -- dune build \
  --root=/tmp/pts-rk-self-open-telescope-pristine.oGwrNN \
  --display=short --no-buffer -j 2 theories/Ranks.vo
timeout 1200 opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-self-open-telescope-pristine.oGwrNN/_build/default/theories PTSrk \
  PTSrk.Ranks

export DIRECT_R_LOCAL_HOME=/Users/akuklev/.local/share/pts-rk-ci
export DIRECT_R_LOCAL_SWITCH=pts-rk-ci
export DIRECT_R_LOG_DIR=/Users/akuklev/air/pts-rk/_build/self-interpreter-open-telescope-final-review.d0SH8N/staged
export DIRECT_R_JOBS=2
export DIRECT_R_STAGE_SECONDS=1200
bash tools/check-local-ci.sh
```

Versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1, opam 2.6.1. Full installed-package inventory is retained.
The driver also compares the original-core kernel inventory with both the
new pristine build and retained
`verification/self-interpreter-2026-10-20/baseline/upstream-kernel.log`;
compares original core, NormalizationComplexity and PR #1 ZFC sources with
`ffa7131`; scans new sources for unsafe/admitted declarations; checks shell
syntax; and compares all frozen source hashes after verification.

## Resource failure and recovery

The initial absolute directory was
`/tmp/pts-rk-self-open-telescope-audit.DTgliS`. Its compiler reported
`Fun.Finally_raised: Sys_error("No space left on device")` and
`dune_trace_write(): No space left on device`. The wrapper was still waiting
on the exact validated Dune process PID 1681 with zombie child processes.
After preserving output and checking its full command, TERM did not stop it;
KILL ended only that owned process. The captured wrapper exit was 137.
No theorem was weakened and no failed output is treated as a verification.

After checking that the failed build was inactive and retaining its trace,
`opam exec -- dune clean --build-dir=/tmp/pts-rk-self-open-telescope-audit.DTgliS`
returned 0, reclaiming approximately 457 MiB. The new retry directory was
empty; it does not reuse any module output from that incomplete attempt.

Parent also reclaimed the completed, validated regenerable caches
`/tmp/pts-rk-local-quotation-spine.nr1PlD` and
`/tmp/pts-rk-telescope-run.QR0a4s` using pinned Dune clean, both exit 0.
The first cleanup crossed a duplicate successful cleanup by this reviewer;
the same cache is not counted twice. Parent's exact logs are
`_build/telescope-run.rwugef/cache-clean-8.log` and `cache-clean-9.log`.
All scoped source/evidence/raw logs live outside these removed caches and
were retained. No active CI or retry-audit cache was removed. Earlier
completed-cache cleanups are recorded in the parent phase evidence.

## Independent contract review

The final construction passed read-only mathematical review. Modules written
by this reviewer also received separate independent reviews from the other
agents; scoped records retain their compile failures and frozen hashes.

- Original typing, annotated syntax and beta-only conversion are unchanged.
  The executable source domain is independent Type-valued derivation data.
  Full propositional coverage uses its inhabitation only inside Prop.
- `RecursiveQuotation.quote_derivation` recurses only on the six original
  rule premises. It does not recursively quote synthesized validity or
  substitution derivations, so the universe-zero case introduces no cycle.
- `ApplicationQuotation` actually allocates two checked equality layers,
  transports retained dependent constructor views and derives the original
  application typing. Its code-alignment witnesses are generated from
  independently typed, strongly recovering endpoints, not supplied as an
  oracle or a target-quotation premise.
- Checked layers enumerate equality-only declarations from numeric bounds.
  Their independently normal closed values erase transport while preserving
  the literal payload. They do not contain a precomputed source semantic
  payload table. Local state extension preserves the literal source context.
- `IndexedProgramInterpreter` evaluates the actual represented PHOAS program.
  Its external indices are ranks and a finite numeric allocation plan, not a
  source term/type/derivation. The represented type is an ordinary argument.
  The extra raw HOAS tag supplies annotation-sensitive fidelity independently
  of conversion repairs.
- `FullDependentInterpreter` discharges construction invariants from the
  actual empty-source state, computed budget and original derivation data.
  Closed coverage has no result-inhabitant premise. Open coverage requires
  the original well-formed context and uses literal closure/reopening.
  Open syntax/conversion fidelity fixes the source arity, while allowing
  different contexts and derivation choices of that arity.
- Full normality, original typing, literal source/type recovery and fidelity
  are proved. No rank-only fragment-uniform decoder, single all-rank program,
  practical enumeration bound or general extraction benchmark is inferred.

The note's positive abstract, full-source theorem and remaining-boundary
sections match these contracts. Stale earlier README remaining-goal paragraphs
were reported to the parent, corrected, and independently reread; the final
positive summary and boundary now agree with the proofs. No claim about the
open material BZC reduction or external
STLC hardness theorem follows from the complete local CI result.
