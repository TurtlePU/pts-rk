<!-- BEGIN DIRECTR CODEX HANDOFF -->
# DirectR: Rocq proof-development instructions

## Read first

This project continues a long ChatGPT discussion. Do not assume that discussion
or its sandbox attachments are available in this session. Read, in this order:
1. `docs/direct-r-handoff/HANDOFF.md`
2. `docs/direct-r-handoff/LATEST_DECISIONS.md`
3. `docs/direct-r-handoff/STATE.md`
4. `docs/direct-r-handoff/MATHEMATICS.md`
Then read the actual `.v` files and the paper's sections 1–5, available as
`docs/direct-r-handoff/reference/Direct_interpretation_of_R_in_PTS_rk.tex`.

The objective is an unconditional, kernel-checked direct interpretation of
classical Tarski–Mostowski–Robinson arithmetic R in the EXISTING PTS-rk calculus.
The project calls this goal “Theorem 5”; locate the paper's `thm:main` label,
not a potentially different printed theorem number.

## Proof integrity

Use the original `PTSrk.Syntax.Term nat n`, `Typing.typ`, and `Ranks.RankSorts`.
Do not change the PTS rules, erase lambda annotations, add primitives,
cumulativity, eta conversion, or strengthen the domain with the result to prove.
No `Admitted`, `admit`, new axioms, unsafe cast shortcuts, disabling guard or
universe checking, or replacing a target theorem by hypotheses that assume it.
Inspect `Print Assumptions` transitively against the upstream baseline.
Never replace the target `typ` judgment by the lab's bidirectional relation.
Native Rocq `Prop` arithmetic can prove numerical side conditions, but does
not itself construct inhabitants of PTS proof types.
A family of finite tests is not a proof over all axiom indices.

## Scope and architecture

Keep the modular native evaluator/checker design and the original kernel.
The lab code can be adapted with provenance; do not import its different PTS
configurations or unfinished metatheoretic contracts as assumptions.
Retain finite arithmetic observations: they construct internal separation
proofs needed for R3 and R4. The external set model is OUT OF SCOPE.
Strong normalization plus preservation and normal-form exclusion can justify
external Bottom-uninhabitation separately; this is NOT a substitute for internal
arithmetic refutations or an internal self-consistency theorem.

## Work and verification

Inspect the checkout, current diff, toolchain, and logs before changing anything.
Build pristine upstream first, then DirectR dependencies in order. Use
`tools/ci-check-direct-r.sh` in its intended Linux/opam environment or the
smaller local build commands documented in the handoff. Fix and recompile one
failure at a time. Do not spend the whole task merely restating the plan.
If compilation is unavailable, state the exact limitation; do not relabel
unexecuted proof scripts as kernel-checked.
Keep failures and timeout results visible. Never weaken CI to obtain green.

## Durable continuity and permissions

Update `docs/direct-r-handoff/STATE.md` after each meaningful milestone and
before ending a session: actual command, exit code, commit/diff state, theorem
status, first remaining goal, log paths, and the next exact command.
Record design changes in `DECISIONS.md`; distinguish facts from proposals.
Do not rely on the chat transcript as the only record.
The user cannot install GitHub CLI. Use ordinary Git and the existing browser-CI
workflow; do not run the archived `publish.sh` or require `gh`.
Do not overwrite user edits, reset a branch, force-push, publish, or merge without
explicit authorization. Never record credentials or private tokens in logs/docs.

<!-- END DIRECTR CODEX HANDOFF -->
