# Reusing the laboratory PTS library in DirectR

## Decision

Use `clayrat/pts-dependent-types` selectively. Its executable, fuel-bounded
checker, successful-run soundness proofs, readable builders, and treatment of
closed certificates are valuable. Do not silently substitute its bidirectional
judgment for the existing `PTSrk.Typing.typ` conclusion.

Reviewed snapshots:

- Laboratory: `clayrat/pts-dependent-types` at
  `7e6282d357c6f42217a9584f6c7493c594ae1aed`.
- Target: `TurtlePU/pts-rk` at
  `723cf2ec61c737ae82ba33d2e7db44f650122b0e`.

This is a source review, not a successful Rocq build. No remote fork, branch,
commit, or PR has been created. The prepared PR remains a local draft package.

## Changes actually made

The local PR source now has an explicit `Codes.NArrow` named-builder constructor,
adapted from the laboratory's `PTS/Named.v`. It resolves both operands in the
same name environment and produces `Π A (shift B)`. It does not allocate a
fresh unused name. The object language remains exactly `PTSrk.Syntax.Term`;
no PTS rule, sort, logical encoding, or primitive is added.

`assemble_nArrow` and two scope regression examples are supplied as Rocq proof
scripts. They have not been compiled. All other typing tactics, arithmetic
proof scripts, and witness generators are unchanged. In particular the
uninhabited `Kernel.Theorem5Target` proof obligation is not hidden or weakened.

The package also contains `review/lab-config/Rank.v` and `RankSmoke.v`, intended
for the LABORATORY repository rather than the target repository. They instantiate
its specification interface with PTS-rk's rules and contain small checking
examples. Their soundness conclusion is explicitly `DepTypes.Bidir.synth`, not
`PTSrk.Typing.typ`. They are not added to the target's Dune dependencies and
have not been compiled.

## Reuse map

| Lab source | Useful content | Recommended action |
|---|---|---|
| `Common/Result.v`, `Common/Traced.v` | Result propagation and traces | Copy with import-path adjustments when introducing the target checker. Preserve provenance from lab `PORTING.md`. |
| `PTS/Eval.v`, `PTS/NormalOrder.v` | Total fuelled evaluation, weak-head inspection, successful-conversion soundness | Adapt the pure algorithms and proofs to `PTSrk.Syntax.Term`, retaining lambda annotations. |
| `PTS/Check.v`, `PTS/CheckSound.v` | Structural recursion, separate expected/synthesized modes, input validation, successful-run theorem | Reuse the architecture and induction pattern; prove success directly against target `Typing.typ`. |
| `PTS/Named.v` | Nonbinding arrow builder, resolution scope lemmas | `NArrow` adapted now. Retain target `close`'s explicit success proof; do not introduce a fallback term for failure. |
| `PTS/SubstLaws.v` | Renaming/substitution algebra | Use as a reference; target already has corresponding laws and typed substitution. Avoid a duplicate syntax foundation. |
| `PCFTranslation/TranslateSound.v` | Certify fixed closed combinators once; lift them to contexts; prove indexed numeral families by induction | Reuse this proof organization for selector arities and continuation spines. Do not reuse its System-U arithmetic as PTS-rk proofs. |
| `Configs/Predicative.v` | Example of a functional infinite sort configuration | Adapt to a distinct `rank_indexed` configuration; do not use the predicative rules themselves. |
| `MLTT/*`, `SystemU/*`, PCF runtime | Primitive or different-system developments | Keep outside the direct-R contribution. |

Source links below are pinned to the reviewed laboratory commit.

## The exact mathematical compatibility issue

### The sort specification fits

Using `Univ i` as a name for `rk_i`, set

```coq
spec_axiom (Univ i) = Some (Univ 0)
spec_rule (Univ a) (Univ b) = Some (Univ (Nat.max (S a) b))
spec_prim = None
```

Only `Univ _` belongs to the specification. `Star`, `Box`, and `Tri` are
rejected. In this configuration `Univ i` names a PTS-rk sort; it does not
retain the meaning of the laboratory's predicative hierarchy. In particular,
there is no cumulativity and no primitive Void, Unit, Bool, or eliminator.

The source `Spec.v` accepts infinite computable functional tables, so there
is no finite-universe truncation requirement. The supplied `Rank.v` also
provides the table-closure proof script.

### The syntax and typing judgments are not identical

The target has intrinsically scoped `Term nat n` with `lam A b`.
The lab has unscoped `term`, `Var : nat -> term`, unannotated `Lam b`,
and an explicit term ascription `Ann t A`. Its reduction also erases an
`Ann` node and includes primitive computation rules in its larger syntax.
Neither difference is merely notation.

Erasing original lambda annotations and running the lab checker cannot
certify the original target term. For example the target term

    lambda x : rk_0. x

has type `Π x:rk_0. rk_0`, not `Π x:rk_1. rk_1`. Both products are already
beta-normal and have distinct domains. But its annotation-erasure `Lam (Var 0)`
checks against either of the two corresponding lab Pi types. This is why
there must be an annotation-preserving bridge or a verified reconstruction
of a target witness; a map on universe labels alone is insufficient.

### What CheckSound proves

The actual lab successful-run theorem is

    run_check ... = Accepted ...
      -> bwf_ctx ... /\ btype ... /\ Bidir.chk ...

It does not conclude the target typing judgment. In `Contracts.v`, the
following are explicitly stated as open contracts, not theorems with
`*_holds` proofs:

- declarative typed weakening and substitution;
- confluence and Pi injectivity;
- `bidir_declarative_sound`;
- soundness of `ConvDifferent` and conversion completeness;
- full checker completeness and normalization for the named configurations.

This is a clear statement of the library's scope, not a reason to discard it.
Successful-run soundness suffices for validating supplied proof candidates.
The open contracts should simply not become assumptions of the direct-R
formalization. The target repository already supplies typed substitution,
confluence, preservation, and strong normalization in its own syntax.

## Recommended substantial next refactor

Port the pure checker to the original target syntax rather than importing
a second PTS kernel. Its key exported statement should have the shape

    accepted (check_rk fuel Gamma p A)
      -> PTSrk.Typing.typ Gamma p A

with the necessary well-formed-input premises or validated input results
made explicit. This is a proposed interface, not a theorem provided by the
present patch.

Start with a total fuel-bounded `head_step` / `whnf` and conversion test.
Prove that a reported equality yields the existing `DefEq.def_equiv`.
For this positive contract, failure or timeout need not prove inequality.
Port the checker-success proof next, using the target constructors and
its proved substitution/subject-reduction lemmas.

There are three concrete improvements over the current Ltac implementation:

1. Use weak-head reduction to expose a product or a sort; do not normalize
   the entire dependent telescope merely to find its head.
2. Test syntactic equality before conversion. Do not normalize an argument
   just to substitute it at beta contraction; evaluate only what checking
   needs. The existing `beta_nf` eagerly normalizes both application children.
3. Treat fuel exhaustion as inconclusive, with diagnostics, rather than an
   infinite tactic run or a mathematical rejection.

After a target soundness theorem is proved, a concrete certificate can be
checked by computation and that theorem, rather than constructing a large
Ltac proof at every beta step. `vm_compute; reflexivity` is appropriate for
such closed successful-run equalities; it is not a proof that all parameterized
generators succeed. No performance benchmark for this proposed replacement
has been run.

## How to finish the uniform interpretation theorem

The most directly relevant model is `PCFTranslation/TranslateSound.v`:
it separates certificates for fixed closed encodings from inductive proofs
for all numeral indices. Apply the same separation to DirectR:

- prove generic well-scoped telescope abstraction/application lemmas;
- prove typing and beta behavior of the q-ary selectors and table application;
- prove the rank-correct selector-domain elimination lemma for arbitrary q;
- derive the 23 law certificates uniformly from capped arithmetic;
- prove the positive invariant and bounded-case generator correct for every n;
- derive all R3, R4, R5 instances and then first-order derivation preservation.

These lemmas must end in the original target typing judgment. The existing
Prop-valued capped arithmetic can supply numerical side conditions, but is
not a replacement for typed PTS witnesses. Likewise, the negative logical
connectives must not be replaced by the lab's primitive positive eliminators.

A stronger target checker will make concrete instances easier to test. It
does not turn finitely many successful checks into the universal
`Kernel.Theorem5Target` record or into a proof of first-order deduction
preservation. Those obligations remain open in the prepared source.

## Verification scope

The small NArrow refactor has independent Python assembly-model regressions
comparing it to the former fresh-name implementation, including lexical
shadowing and failure on unbound names. The companion PTS checker was also
rerun on the generator declarations; those declarations are unchanged.
The detailed reports are in `review/checks/`. They do not execute Gallina,
Ltac, or a Rocq kernel check. Neither repository could be built here because
a Rocq toolchain is absent and direct network downloads are unavailable.

No nontriviality theorem for the answer type, set model, extra PTS axiom, or
assumption asserting the desired interpretation is introduced.

## Sources

- [Spec.v](https://github.com/clayrat/pts-dependent-types/blob/7e6282d357c6f42217a9584f6c7493c594ae1aed/theories/PTS/Spec.v)
- [Syntax.v](https://github.com/clayrat/pts-dependent-types/blob/7e6282d357c6f42217a9584f6c7493c594ae1aed/theories/PTS/Syntax.v)
- [Named.v](https://github.com/clayrat/pts-dependent-types/blob/7e6282d357c6f42217a9584f6c7493c594ae1aed/theories/PTS/Named.v)
- [Eval.v](https://github.com/clayrat/pts-dependent-types/blob/7e6282d357c6f42217a9584f6c7493c594ae1aed/theories/PTS/Eval.v)
- [Check.v](https://github.com/clayrat/pts-dependent-types/blob/7e6282d357c6f42217a9584f6c7493c594ae1aed/theories/PTS/Check.v)
- [CheckSound.v](https://github.com/clayrat/pts-dependent-types/blob/7e6282d357c6f42217a9584f6c7493c594ae1aed/theories/PTS/CheckSound.v)
- [Bidir.v](https://github.com/clayrat/pts-dependent-types/blob/7e6282d357c6f42217a9584f6c7493c594ae1aed/theories/PTS/Bidir.v)
- [SubstLaws.v](https://github.com/clayrat/pts-dependent-types/blob/7e6282d357c6f42217a9584f6c7493c594ae1aed/theories/PTS/SubstLaws.v)
- [Contracts.v](https://github.com/clayrat/pts-dependent-types/blob/7e6282d357c6f42217a9584f6c7493c594ae1aed/theories/Contracts.v)
- [TranslateSound.v](https://github.com/clayrat/pts-dependent-types/blob/7e6282d357c6f42217a9584f6c7493c594ae1aed/theories/PCFTranslation/TranslateSound.v)
- [Predicative.v](https://github.com/clayrat/pts-dependent-types/blob/7e6282d357c6f42217a9584f6c7493c594ae1aed/theories/Configs/Predicative.v)
- [PORTING.md](https://github.com/clayrat/pts-dependent-types/blob/7e6282d357c6f42217a9584f6c7493c594ae1aed/PORTING.md)
