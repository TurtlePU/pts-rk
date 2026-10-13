# Decisions and proof-engineering history

## 2026-10-13 — imported handoff

- Keep TurtlePU's original scoped beta-only PTS kernel.
- Use arithmetic-expression presentations and certified observations directly;
  no intermediate WF- interpretation.
- Use the modular native target evaluator/checker design; lab code can be
  adapted, not trusted as a bridge to the original typing judgment.
- Keep the section-3 finite observations for INTERNAL arithmetic refutations.
- Reduce the separation API to no_back_n if that simplifies the uniform proof.
  This is a proposed code refactor with an on-paper argument, not compiled yet.
- Set models are excluded. External Bottom-uninhabitation can be a separate
  corollary of normalization/preservation/canonical shapes, not a prerequisite.
- No uniform Theorem 5 proof or successful Rocq build was recorded in this chat.
- User uses ordinary Git and browser GitHub Actions, not gh.

Append dated entries for substantive changes: decision, reason, alternative
rejected, actual evidence and affected theorem statements. Avoid claiming that
an architectural change has been verified before compiling it.

## 2026-10-13 — CI toolchain and local checks

- CI now pins Rocq core 9.2.0, Stdlib 9.1.0, and Equations 1.3.2+9.2.
  The historical upstream uses `Create Rewrite HintDb`, introduced in 9.2;
  run 38328517931 failed parsing it under 9.1.1. The unchanged baseline
  compiled under the updated local toolchain.
- Installed a dedicated native ARM OCaml 4.14.2 switch and matching static
  GMP 6.3.0. Existing Intel Homebrew GMP cannot link with the ARM compiler.
  Local checks use actionlint followed by the actual CI build driver, rather
  than treating YAML parsing alone as workflow validation.
- Repaired evaluator/checker scripts with explicit case analysis, correct
  indexed induction patterns, and properly constrained theorem applications.
  No statements, target rules, assumptions, or checking flags changed.
  Their main soundness theorems compile and report no global assumptions;
  see STATE.md and the infrastructure assumption transcript.
- DirectRCodes excludes Syntax's notation category to avoid the upstream
  lambda/list parser conflict. It still imports the original constructors
  and definitions. DirectRProofs supplies the closed application parameters
  explicitly to `fold_left`.
- An experiment reusing fixed certificate hypotheses in the symbolic tactic
  exposed a further opaque-numeral typing problem and was reverted. Repairing
  that symbolic induction layer remains pending; no uniform theorem completion
  is claimed.
