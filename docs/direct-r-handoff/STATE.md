# Live proof-development state — update this, do not rely on session memory

## Handoff baseline (2026-10-13)

- Active user checkout / branch / commit: NOT INSPECTED by this handoff.
- Remote fork / PR URL: NOT VERIFIED. Local packages only were prepared in chat;
  user may since have applied/pushed them. Inspect before claiming anything.
- Last successful Rocq build of DirectR recorded in chat: NONE.
- Latest source: modular `DirectR_restructured_PR_package.zip` plus CI add-on.
- Uniform GeneratorTotal / GeneratorSound: NOT PROVED in that snapshot.
- Unconditional Theorem5Target: NOT CONSTRUCTED.
- Source deduction judgment and preservation: NOT COMPLETED.
- Ground faithfulness as uniform object-language realization/refutation: OPEN.
- External model / Bottom nontriviality: OUT OF SCOPE, not prerequisites.
- Last design updates: LATEST_DECISIONS.md.
- Independent tests: older Python/static tests, NOT compiler evidence.

## Current environment and verified checkout

Fill from actual commands; do not repeat stale assumptions from the old container.

- Commit: `cb79586d0d9bfcf1835e32e9c2563bc445cf9d24` (user's AGENTS update),
  on top of amended/pushed `9e01435086ae930267a778b253b497281e738742`.
- Branch: `main`.
- User changes to preserve: rewritten `AGENTS.md`, newly supplied
  `docs/direct-r-handoff/`, and downloaded `logs/` artifacts.
- Compiler / Dune / Equations versions: locally installed OCaml 4.14.2,
  Rocq core/runtime 9.2.0, Stdlib 9.1.0, Dune 3.23.1,
  Equations 1.3.2+9.2, opam 2.6.1, actionlint 1.7.12.
  Native ARM GMP 6.3.0 was built because Homebrew's GMP is Intel-only.
- Local environment: `$HOME/.local/share/pts-rk-ci`, opam root `opam/`,
  named switch `pts-rk-ci`, downloaded tools in `bin/`, native GMP in `native/`.
- Relevant active AGENTS files / overrides: root `AGENTS.md` and its
  DirectR handoff instructions; current task is CI repair/local environment
  setup, not completion of all Theorem 5 mathematical obligations.
- CI run URL and checked commit:
  https://github.com/akuklev/pts-rk/actions/runs/38331028223,
  `9e01435086ae930267a778b253b497281e738742`. Toolchain installation,
  pristine upstream, and kernel passed; `03-evaluator` failed.

## Latest actual build

- Command: `DIRECT_R_STAGE_SECONDS=60 bash tools/check-local-ci.sh`
  (workflow lint plus the actual CI driver, with a local diagnostic time limit).
- Exit code: 124 (timeout) at `07-proof-families`. The committed CI limit remains
  1200 seconds per stage; this local run does not prove a typing rejection.
- Passed stage(s): 01 isolated upstream, 02 kernel, 03 evaluator, 04 checker,
  05 codes, and 06 symbolic.
- First failing file / line / theorem: initial local run reproduced
  `DirectREval.v`, `head_step_sound`: incomplete proof. Repaired the evaluator
  and checker scripts without changing statements or adding assumptions.
  Latest downstream source repair was `DirectRProofs.v:160`, a partially applied
  `app` in `fold_left`; changed it to `@app nat 0`. The remaining slow proof is
  `observed_numeral_typed`, whose successor goal is
  `Typed ε (observed_numeral (S n)) (GAt (numeral (S n)))`.
- Exact error or proof goal: the final driver run timed out in proof families.
  A timed compiler investigation reached `observed_numeral_typed`; see the next
  checkpoint for the opaque-numeral failure in the reverted experiment.
- Log path: `_build/local-ci-logs/` for the staged runs; targeted compiler
  diagnostics in `_build/log` and terminal output.
- Were remaining stages run? Stages 08–13 were not checked; the driver stopped
  at stage 07. No overall green build is recorded.

## Proven versus pending

The local evaluator/checker repairs preserve the existing statements. At
`cb79586` plus the working diff, `dune build theories/DirectREval.vo
theories/DirectRCheck.vo` compiled, and the following assumption queries all
returned `Closed under the global context`:

- `RkEval.head_step_sound`: `head_step t = Some u -> t →ᵝ u`.
- `RkEval.normal_step_sound`: `normal_step t = Some u -> t →ᵝ u`.
- `RkEval.convert_equal_sound`: `convert fuel A B = ConvEqual -> A =ᵝ B`.
- `RkCheck.run_check_sound`:
  `run_check fuel G t A = Accepted tt -> Core.Typed G t A`.

Here `t`, `u`, `A`, and `B` have the original `Term nat n` type, `G : Ctx nat n`,
and all scope/fuel variables are universally quantified as in the source.
The upstream `Ranks.strong_normalization` query also returned `Closed under the
global context`. Transcript: `_build/local-ci-logs/infrastructure-assumptions.log`.

The uniform generator contracts, unconditional Theorem5Target, full ground
faithfulness, and first-order deduction preservation remain open. Passing
infrastructure compilation does not discharge them.

## Next checkpoint

- Next exact command: `bash tools/check-local-ci.sh` from the repository root.
  To focus on the remaining module:
  `OPAMROOT="$HOME/.local/share/pts-rk-ci/opam" "$HOME/.local/share/pts-rk-ci/bin/opam"
  exec --switch=pts-rk-ci -- dune build theories/DirectRProofs.vo`.
- Next mathematical lemma: `Kernel.observed_numeral_typed`; its induction step
  must retain typing evidence for symbolic numerals through substitution/lifting.
- Why it is needed: all ground calculation families and downstream generators
  depend on the proof-families module.
- Current attempted proof and its concrete failure: symbolic `certify` is slow
  on the successor step. An experiment supplying already checked closed typing
  lemmas failed with `DirectR: no typing hypothesis for opaque expression`
  on the unfolded `numeral n`. That experiment was reverted; simply adding
  the fixed certificates does not fix opaque terms under extended contexts.
  A direct pair of `tApp` applications also does not convert automatically to
  the expected type: structural substitution/renaming must be simplified by
  proved syntax lemmas.
- Files changed: `DirectREval.v`, `DirectRCheck.v`, `DirectRCodes.v`,
  `DirectRProofs.v` (explicit `@app nat 0` only), `docs/DirectR-CI.md`, new
  `tools/check-local-ci.sh`, and this live state file. User handoff/AGENTS edits
  are preserved. The local setup/proof repairs are not committed or pushed.
- Unsuccessful approaches worth remembering: the evaluator's original matching
  only inspected explicit option matches, missing `option_map`. Unconstrained
  `eapply rtc_step` did not determine its intermediate term. Checker induction
  patterns omitted the explicit scope index on every constructor. Importing all
  Syntax notations breaks list patterns in DirectRCodes; excluding only the
  notation category fixes the assembler without changing upstream Syntax.

Before ending a session, replace blanks with the current state or explicitly
say “not yet run / unknown.” Keep detailed work history in DECISIONS.md or logs.
