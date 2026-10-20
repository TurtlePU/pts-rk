# Elementary representability: source audit, 2026-10-20

Read-only mathematical/source audit by the independent audit agent. This report
is the only file added by this audit; the manuscripts and proofs were not
changed. Audited HEAD: `73c4303dca2228bb6b3a8ec6ba5099a86da00bb0`, with the
in-progress self-interpreter worktree retained. No Rocq compilation or new
kernel/assumption check was run for this source-only audit.

## Exact claim and formalization boundary

- `latex/paper.tex`, theorem label `non-uniform-rep` (line 1687), and the
  corresponding `latex/PTS-rk.tex` label `{#non-uniform-rep}` (line 1670), state:
  every elementary recursive `f : N^n -> N` has a cost `c_f` such that, for
  each base rank `j`, an original PTS term represents it at
  `N_(j+c_f) -> ... -> N_(j+c_f) -> N_j`, with beta-conversion correctness on
  Church numerals. Here `N_j = Pi(X:U_j). (X->X)->X->X` has sort `U_(j+2)`.
- The proof describes addition, multiplication, rank-changing exponentiation,
  numeral-preserving lowerings, and modulus. Its elementary substitution-basis
  result is an external citation, `prunescu2026minimal` in
  `latex/bibliography.bib` (arXiv:2505.23787). This audit did not independently
  verify that external basis theorem.
- The rank cost can be computed from a **supplied expression in the stated
  elementary basis**: for composition `h(g_1,...,g_k)`, a sufficient cost is
  `c_h + max_i c_(g_i)`, using lowerings to align inputs. This is not an
  algorithm extracting such an expression from an arbitrary extensional
  elementary function or an arbitrary program. For positive arity the
  displayed representation's function type has sort `U_(j+c_f+3)`; a nullary
  result has type `N_j : U_(j+2)`. These are source-level rank calculations,
  not the output of a checked compiler.
- `latex/ROCQ_REFERENCES.md`, section "Complexity and representability"
  (lines 63--77), explicitly records **no exact formal theorem** for
  `non-uniform-rep`, `uniform-elementary`, `rep-bound`, the exact elementary
  representability corollary, or even the generic all-rank polymorphic numeral
  family. The source search found no general elementary-expression-to-original-
  PTS compiler or accompanying correctness/rank theorem.

## Concrete manuscript error (not changed)

The final modulus callback in `latex/paper.tex:1895` and
`latex/PTS-rk.tex:1891` applies the record component as `r X f x`.
The displayed handler type assigns that component the already-specialized
type `(X -> X) -> X -> X`; it is not polymorphic in `X`. The callback must
therefore use **`r f x`**. The existing `r_0 = delta_j m X` and
`r^+ = rho (m S c z)` also have that specialized type. The extra `X` makes the
displayed modulus term ill-typed as written. This observation does not certify
the rest of the informal modulus proof. Its advertised carrier ranks
`H_X : U_(j+3)` and `P_X : U_(j+4)` are consistent with the displayed types.

## What the checked neighboring results do establish

- `theories/NormalizationComplexity/BoundedNormalization.v`,
  `fixed_rank_normalization` (line 19), assumes original `wf G`, original
  `typ G t T`, and independent `RedexBound G t d`. It returns a beta-normal
  original term of the same type, forward reduction from `t`, and native
  reducer cost bounded by `tower (2*d+1) (nodes t+5*d+2)`. The bound covers
  annotations. This is an external executable normalization theorem in the
  documented operation-cost model, **not** an original PTS inhabitant
  implementing the numerical normalization function.
- `Normalization.normalization_in_TOWER` supplies an automatic bound for
  every closed original typed input, using
  `rounds (AutomaticBound.conservativeRank t) t`. These upper bounds do not
  provide arbitrary elementary-function representability. An exact sort
  needed by an object-language type cannot be replaced by a larger bound:
  the original PTS has no cumulativity rule.
- `theories/Interpretation_of_R/functional/DirectRTheorem7.v`,
  `effective_axiom`, `effective_source_axiom`, `effective_deduction`,
  `effective_ground_true`, `effective_ground_false`, and `theorem7`
  (lines 56--75), construct annotated inhabitants of translated arithmetic
  statements. Their witness search is certificate enumeration with a
  termination argument from existence, not a general elementary numeric
  compiler or an elementary runtime guarantee.
- `PTS_rk_interprets_Tarski_Mostowski_Robinson_arithmetic_R_harmonized.tex`,
  section label `sec:operators` (line 494; explanation at lines 503--528),
  explicitly distinguishes four-constructor arithmetic **expression
  presentations** and equations proved in observational equality `E_a` from
  beta-computation on canonical numerals.
- `theories/Interpretation_of_R/relational/DirectRUnaryEvaluation.v`,
  `addition_numerals` (line 109) and `multiplication_numerals` (line 151), do
  prove numeral beta-computation. They use a fixed-rank unary carrier, not
  the manuscript's generic `N_j` family or an elementary-function compiler.
- `theories/NormalizationComplexity/STLCEmbedding.v`,
  `church_stlc_reduction` (line 198), checks a Church-STLC embedding with
  original typing, conversion preservation/reflection, and size accounting.
  The source STLC TOWER-hardness theorem remains external. Neither theorem
  supplies the missing elementary representability direction.

## Reproduction commands

The following read-only commands were used from the repository root. `rg`
matches and the `sed` reads succeeded (exit 0). The `command -v` probe found no
`jbcontext`; the requested semantic-search skill therefore used its documented
fallback to `rg`. No compiler verification is claimed by these commands.

```sh
command -v jbcontext || true
git rev-parse HEAD
git status --short -- docs/direct-r-handoff/verification/self-interpreter-complexity-2026-10-20 theories/self_interpreter latex/paper.tex latex/PTS-rk.tex latex/ROCQ_REFERENCES.md
sed -n '63,80p' latex/ROCQ_REFERENCES.md
rg -n 'non-uniform-rep|uniform-elementary|rep-bound' latex/paper.tex latex/PTS-rk.tex latex/ROCQ_REFERENCES.md
sed -n '1679,1715p' latex/paper.tex
sed -n '1838,1898p' latex/paper.tex
sed -n '792,810p' latex/bibliography.bib
sed -n '1,65p' theories/NormalizationComplexity/BoundedNormalization.v
rg -n 'effective_axiom|effective_source_axiom|effective_deduction|effective_ground_true|effective_ground_false|Theorem theorem7|addition_numerals|multiplication_numerals|church_stlc_reduction' theories/Interpretation_of_R/functional/DirectRTheorem7.v theories/Interpretation_of_R/relational/DirectRUnaryEvaluation.v theories/NormalizationComplexity/STLCEmbedding.v
rg -n 'sec:operators|observational|presentation' PTS_rk_interprets_Tarski_Mostowski_Robinson_arithmetic_R_harmonized.tex
```

Conclusion: the second premise has an explicit manuscript theorem and
constructive outline, with the concrete typo above, but **no matching Rocq
compiler/representability theorem in the audited repository**. A
normalization-assisted packet carrying a precomputed normal payload and a
faithful HOAS tag can be developed independently; it must not be described
as a pure HOAS evaluator or as a formalization of this missing premise.
