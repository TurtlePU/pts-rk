# DirectR — authoritative handoff from ChatGPT to Codex CLI

Prepared 2026-10-13. This is a curated project handoff, not a verbatim transcript
or a proof certificate. Its facts describe the supplied archive snapshot, not
an uninspected current checkout or GitHub run. Live source and actual kernel
output must settle implementation questions.

## 1. User's objective

Finish the direct interpretation of classical Tarski–Mostowski–Robinson
arithmetic R in PTS-rk in Rocq, fitting TurtlePU's existing repository.
Do not go through weak finite-multiset theory WF-. Do not formalize a
set-theoretic model. The desired endpoint includes uniformly typed closed
witnesses of all five R schemes, admissibility of classical first-order
reasoning under the guarded negative translation, and ground faithfulness.

“Theorem 5” is the project's name for the main theorem in
`reference/Direct_interpretation_of_R_in_PTS_rk.tex`, label `thm:main` in the
section “Verification of the interpretation.” Printed numbering may vary.
Identify it by its statement and label.

The user owns account `akuklev`, intends to use a fork and GitHub CI, and cannot
install GitHub CLI. Ordinary Git, browser-based fork/PR creation, and downloading
CI logs are the established workflow. Do not claim a fork or PR exists without
checking. The preparation recorded in this chat created local packages only;
the user's subsequent remote activity is unknown.

## 2. Repository and reference snapshots

Target: `https://github.com/TurtlePU/pts-rk`
- Inspected base: `723cf2ec61c737ae82ba33d2e7db44f650122b0e`.
- Namespace: `PTSrk`.
- Core files: Syntax, Context, Typing, Reduction, DefEq, Inversions,
  Preservation, SN, Ranks.
- Existing context/substitution/confluence/normalization results are to be
  reused, not replaced by invented wrappers around a different calculus.
- `theories/dune` explicitly enumerates modules.
- The snapshot's dune-project says `(lang dune 3.23)` and `(using rocq 0.13)`.

Lab: `https://github.com/clayrat/pts-dependent-types`
- Reviewed snapshot: `7e6282d357c6f42217a9584f6c7493c594ae1aed`.
- The user authorizes copying/modifying lab files. Preserve provenance and any
  applicable notices; this authorization is not a reason to erase attribution.
- Use only relevant PTS evaluator/checker/builder/proof-engineering components.
- Reinspect revisions before adapting code; the snapshot is not a claim of
  current main's contents.

The two latest original packages are included byte-for-byte in `inputs/`.
They are recovery inputs, not files to apply blindly over an existing branch.
Older monolithic DirectR.v packages are superseded.

## 3. What is actually present, and what is not verified

The latest package has NOT had a successful Rocq build recorded in this chat.
Even the written R1/R2 scripts and native checker-soundness scripts are
compiler-unchecked. `Qed` source text is not evidence that the kernel accepted
it. A later real CI run may supersede this status; record its commit, versions,
command, result, and logs in STATE.md rather than guessing.

The package contains:
- Fixed intrinsically scoped PTS codes for D, Good, observations, E/O/G, and the
  translated axiom types.
- Candidate closed terms exposing observation laws and domain certificates.
- Induction scripts for uniform object-language ground addition, multiplication,
  and order calculations.
- Executable variable-arity generators for selectors, all 23 observation laws,
  the positive invariant, the bounded-case lemma, and R3–R5 witnesses.
- A native fuelled evaluator/checker with proof scripts intended to conclude
  the ORIGINAL typing judgment; success soundness still awaits compilation.
- Scoped first-order syntax and its formula translation, but no complete source
  proof system/soundness theorem.
- Separate native-Prop arithmetic facts and concrete test scripts.

Past Python checks exercised some object terms, finite tables, name assembly,
patch application, and module splitting. They did NOT run Gallina/Ltac or
validate Rocq proof objects. The latest modular package's full independent
rerun timed out; do not conflate earlier small tests with a full successful run.

## 4. Module map (current prepared package)

| Module | Responsibility |
|---|---|
| DirectRKernel | Original typ/definitional-equality API wrappers, module Core |
| DirectREval | Fuel-bounded reduction and positive conversion-soundness scripts |
| DirectRCheck | Native checker, validated inputs, positive acceptance theorem |
| DirectRCodes | Named assembler, fixed PTS codes and axiom-type constructors |
| DirectRSymbolic | Legacy proof-producing tactics retained for symbolic indices |
| DirectRProofs | Closed certificates and indexed ground calculations; module Kernel |
| DirectRGenerated | Arity/cutoff-dependent candidate proof-term generators |
| DirectRFirstOrder | Source term/formula syntax and deep translation |
| DirectRObligations | Stated totality/typing contracts and conditional packaging |
| DirectRArithmetic | Native Rocq arithmetic, separate from PTS inhabitation |
| DirectRTests | Concrete checks and assumption-printing commands |
| DirectR | Public facade, not importing tests/native-Prop arithmetic |

The facade's Kernel aliases `DirectRProofs.Kernel`. Do not confuse it with
`DirectRKernel.Core`. Inspect actual definitions before writing imports.

## 5. Precise unfinished contracts

The original code defines these goals without proofs:

```coq
Definition GeneratorTotal : Prop :=
  forall a, exists p, Generated.witness a = Some p.

Definition GeneratorSound : Prop :=
  forall a p, Generated.witness a = Some p ->
    Typed ε p (axiom_type a).

Record Theorem5Target : Type := {
  axiom_witness : axiom_instance -> closed_term;
  axiom_witness_typed : forall a,
    Typed ε (axiom_witness a) (axiom_type a)
}.
```

`target_from_generator_contracts total sound` is deliberately conditional.
It does not prove either input. `select_witness` has a syntactic fallback;
only a totality proof could make the failure branch unreachable and justify
its claimed realization. Never certify the fallback as a substitute for the
requested axiom witness.

It is permissible to refactor generators into intrinsically typed constructions
rather than prove these particular implementation contracts, provided the
unconditional theorem still realizes the SAME specified interpretation and
all unbounded external indices. Document any equivalent replacement explicitly.

Remaining tasks:
1. Compile and repair the infrastructure and existing scripts.
2. Prove uniform scope/totality or construct total well-scoped witnesses directly.
3. Prove all-arity telescope, selector, table, domain-elimination, and observation
   law realization lemmas against typ.
4. Prove all-cutoff invariant/bounded-case realization for arbitrary admitted
   d:D with Good(d), not just external expression trees.
5. Obtain uniform R3/R4/R5 and an unconditional Theorem5Target.
6. Prove ground-expression equality to its value numeral and all ground
   equality/order truths and refutations.
7. Define a precise independent classical first-order deduction system and prove
   preservation, including domain obligations, equality replacement, stability,
   and translation/substitution under guarded quantifiers.
8. Build and audit assumptions for the final PUBLIC statements. Update CI so
   it requires those statements, not just modules containing open definitions.

No theorem may define source provability as target inhabitation or postulate
the interpretation in a record field to call the task complete.

## 6. Why the lab is used selectively

The lab uses unscoped de Bruijn terms, unannotated Lam bodies, term-ascription
Ann, and an extended syntax of primitives. The target uses `Term nat n`,
`Fin n`, and `lam A b` with its domain annotation retained.
Erasing the domain can cause the lab to accept a DIFFERENT target annotation:
`lambda x:rk_0. x` cannot thereby be certified at `rk_1 -> rk_1`.

At the reviewed lab snapshot, `run_check_sound` ends in its bidirectional
`chk` relation; the declarative bridge and other metatheoretic contracts are
explicit open obligations. Do not treat those declarations as proved lemmas.
Use native target checking/proofs instead. Its intended accepted-run contract is
`run_check fuel Gamma p A = Accepted tt -> Core.Typed Gamma p A`, with input
validation. Checker completeness is not necessary to certify successful runs.
Fuel exhaustion is not a mathematical rejection. Our fixed certificate budgets
4096 and concrete-example budgets 65536 are proposals, not measured successes.

The explicit NArrow builder has already been adapted: resolve both operands in
the same environment, then construct Pi A (shift B). It is assembler syntax,
not a new PTS constructor.

## 7. First work session

Read STATE.md and inspect git status, actual source, branch, remotes (without
exposing credentials), tool versions, and any available CI logs. Preserve user
changes. Do not reset to the historical base just because this handoff names it.

Compile pristine upstream, then native infrastructure, then the interpretation
modules. Fix the first actual error and rerun the affected stage. Preserve exact
commands and output paths. Reinspect the theorem types after fixes. Continue
with one uniform proof layer at a time rather than producing another large
uncompiled replacement. See BUILD.md for the prepared build commands.

The mathematics in MATHEMATICS.md is an on-paper plan, not a machine-checked
fact. If formalization exposes a real flaw, state its exact smallest lemma and
repair the argument without silently strengthening the PTS or weakening the
interpretation. Do not substitute an external model for internal proof terms.

## 8. Out of scope

Do not reopen the long manuscript's internal arithmetized self-consistency
argument, the global logical upper-bound conjecture, local finite satisfiability,
CZF/Zermelo models, or rank-preserving arithmetic impossibility results. None
is a premise of the present direct-R witness construction. In particular,
ordinary external Bottom-uninhabitation and an internal Hilbert-consistency
sentence are different results.
