# FiniteHorn isolated proof development, 2026-10-23

Working directory: `/Users/akuklev/air/pts-rk`.
Only new project source `theories/CombinatoryLogic-rk/FiniteHorn.v` was edited.
Existing dirty files were inspected and preserved. No staging or commit.

Environment for compiler commands:

```sh
env PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH" \
  OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci \
  opam exec -- rocq compile \
  -Q _build/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -Q /tmp/pts-rk-finite-horn.sct6i1 PTSrk.Combinatory \
  -o /tmp/pts-rk-finite-horn.sct6i1/FiniteHorn.vo \
  theories/CombinatoryLogic-rk/FiniteHorn.v
```

Attempts 04–07 used exactly that compiler command. Attempt 02 omitted the
second `-Q`. Attempt 03 additionally mapped the project source directory
to the same namespace instead of mapping the temporary output directory.
Each attempt redirected stdout/stderr to the correspondingly numbered log;
the shell printed the actual compiler exit independently of its own exit.

| Attempt | Exit | Result |
| --- | --- | --- |
| 01 | 127 | `env PATH=...:$PATH` was unquoted; spaces in the inherited PATH split arguments. Compiler was not invoked. |
| 02 | 1 | Initial `rounds_closed` stationary case failed at `lia`. Also output namespace mapping emitted the masking warning. |
| 03 | 1 | Explicit list arguments to `NoDup_length_incl` were implicit arguments; same namespace warning. |
| 04 | 1 | Stationary case needed closure of the original list before applying `closed_rounds (S k)`. Namespace mapping corrected, no warning. |
| 05 | 1 | `round_sound` needed explicit pointwise use of `Forall_forall`; remaining subgoal. |
| 06 | 0 | Initial complete saturation/denial/model interface; eight closed assumption reports, no warnings. |
| 07 | 0 | Final signed-diagram, formula-reflection, source-soundness and regression additions; sixteen closed reports, no warnings. |

The isolated compile imports the existing built `GroundHorn.vo` and Stdlib;
it is not claimed as a fresh full project or dependency-closure build. The
root agent is responsible for fresh registration/build/recheck after its
parallel GroundHorn changes. The final new source has no postulates or
admitted proofs; all sixteen printed transitive assumption reports are closed.

Public results:

- `rounds_closed`: closure after at most as many rounds as rule heads.
- `saturation_exact`, `saturation_least`, `saturation_size`: exact derivation
  reflection for every atom, least positive model, size at most clause count.
- `denial_model_exists_iff`: executable check iff a denial-constrained model
  exists; `denied_atoms_empty` applies to every such model.
- `constrained_consequence_exact`: all-model positive consequence is exactly
  derivability when the denial check accepts.
- `fixed_finite_model`: actual unit domain, every domain assignment, all clauses
  and denials; interpretation is the computed saturation.
- `completed_model_exists_iff`, `completed_formula_reflection`, and
  `completed_formula_consequence`: finite signed diagram and complete truth
  reflection for every supported propositional formula. Negative literals
  are added by completion, not asserted to follow from the positive theory.
- `saturation_source_sound`: transport into a separately supplied source rule
  system containing the finite clauses; no converse adequacy assumption.
- Five executable regression examples (chain, unsupported cycle, accepted
  denials, rejected denial, negative formula evaluation).

No statement here constructs a finite model of the original ungrounded PTS
signature or an internal PTS consistency proof.
