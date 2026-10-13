# Live proof-development state — 2026-10-13

## Current continuation: finite recursion equations, following 281a252

Request: retry push, proceed proving, commit and push. Starting HEAD was
281a252cd48a8f7bc43ef1174da29a219e744076 on main. Only untracked user logs/
was present and is preserved. The prior push stalled in macOS Keychain and was
terminated (143); this session's `timeout 45 git push origin HEAD:main` exited 0
and pushed 281a252 to origin/main. Theorem 7 is NOT complete.

Complete baseline local CI, including pristine upstream, exited 0:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/recursion-laws-baseline"
bash tools/check-local-ci.sh`, with the documented local bin directory on PATH.
Raw log: _build/local-ci-logs/recursion-laws-baseline.log.

New checked modules:
- DirectRFiniteExpressions proves original PTS typing, substitution compatibility,
  bounded numerical evaluation and beta evaluation for nested finite-table
  expressions in two variables. This auxiliary syntax does not change D.
- DirectRFiniteRecursionLaws compiles a numerical equation valid on all selector
  pairs into a closed guarded PTS equality certificate. The two public instances
  have only the premise q>0, and realize the expanded types:

```
Pi u:Fq. delta(u) -> Pi v:Fq. delta(v) ->
  Neg(R0 (add (s u) v) (s (add u v)))
Pi u:Fq. delta(u) -> Pi v:Fq. delta(v) ->
  Neg(R0 (mul (s u) v) (add v (mul u v)))
```

Here s/add/mul are capped tables and R0 is the finite equality test. The
public names are addition_successor_realized and multiplication_successor_realized.
Their expanded types have checked rank five and retain both domain guards.
The generic equation_realized uses native equations only to build the selector
branch proofs, followed by original PTS positive-membership elimination.

Incremental command (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short
--no-buffer theories/DirectRFiniteRecursionLaws.vo`.
Exit-0 log: _build/local-ci-logs/recursion-laws-3.log. Earlier compiler errors
are retained in recursion-laws-1.log (beta_app needed eapply for its intermediate
term) and recursion-laws-2.log (the capped identities live in CappedArithmetic,
not ArithmeticCore). No error was bypassed or admitted.

Fourteen of nineteen relational observation certificates are now proved,
including all five arithmetic equations. Five order-propagation laws remain.
Full observation assembly, negative ground faithfulness, the four-constructor
bounded invariant, and independent functional deduction preservation remain open.
The external set model is out of scope under the replacement AGENTS instructions.

Exact next goal: uniformly for q>0, construct
`Pi u:Fq. delta(u) -> Neg(C0 u (s u))`, where C0 is the finite order test.
Use a rank-two unary family and guarded_finite_realized. The point branch is
i <= min(S i,pred q), for i<q; construct negative_true after checked table
conversion. Then compile the two addition and two conditional multiplication
order-propagation laws with the finite-expression evaluator.

Next command after implementing the next law (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short
--no-buffer theories/DirectRFunctionalAudit.vo`.
Fresh isolated full build exited 0, including all legacy examples:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- timeout 300 dune build \
  --build-dir /tmp/pts-rk-recursion-laws.3JZyHM --display=short --no-buffer
```

All 170 assumption reports are closed (62 in the functional audit). The exact
public theorem types, expanded definitions and output are retained in
verification/recursion-laws-full-2026-10-13.log; raw output is in
_build/local-ci-logs/recursion-laws-full.log. Complete updated local CI also
exited 0, including pristine upstream and the two new stages:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/recursion-laws-final"
bash tools/check-local-ci.sh`. Its inventory and results are retained in
verification/recursion-laws-ci-2026-10-13.log and raw
_build/local-ci-logs/recursion-laws-ci.log. Shell syntax, actionlint and
git diff --check pass. Remote CI has not been inspected. This checked progress
checkpoint follows 281a252 and is authorized for ordinary commit and push.

## Historical continuation: finite zero laws, following 9ef8568

Request: proceed proving Theorem 7, commit and push. Starting HEAD was
9ef85681155441855a38295ba6c077b3705d38a0 on main. Only the user's untracked
logs/ was present; it is preserved and excluded from the commit.
Theorem 7 is NOT complete. The original functional interpretation is unchanged.

Baseline complete local CI driver, including pristine upstream, exited 0:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/arithmetic-laws-baseline"
bash tools/check-local-ci.sh` with the documented local bin directory on PATH.
Raw log: _build/local-ci-logs/arithmetic-laws-baseline.log.

DirectRFiniteZeroLaws now constructs three original PTS inhabitants, for every
q>0, of these expanded closed types (R0 is the finite equality test):

```
Pi u:Fq. delta(u) -> Neg(R0 (add (point q 0) u) u)
Pi u:Fq. delta(u) -> Neg(R0 (mul (point q 0) u) (point q 0))
Pi u:Fq. delta(u) -> Neg(R0 (mul u (point q 0)) (point q 0))
```

The public theorems are addition_zero_realized,
multiplication_zero_left_realized and multiplication_zero_right_realized.
Their only premise is 0<q. Generic zero_law_realized accepts a typed binary
operation and its pointwise beta action; the public laws discharge both using
the existing capped tables. expanded_type_typed proves exact rank five and
expanded_type_beta preserves annotations and the interleaved domain guard.

The first incremental build exited 0, without any compiler-error iteration:
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short
--no-buffer theories/DirectRFiniteZeroLaws.vo` with documented OPAMROOT/PATH.
Output: _build/local-ci-logs/zero-laws-1.log.

Fresh isolated full build exited 0, including all legacy examples:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- timeout 300 dune build \
  --build-dir /tmp/pts-rk-zero-laws.cYmQHT --display=short --no-buffer
```

All 162 assumption reports are closed (54 in the functional audit). The public
theorem types, expanded definitions and fresh output are retained in
verification/zero-laws-full-2026-10-13.log; raw output is in
_build/local-ci-logs/zero-laws-full.log. Complete updated local CI also exited 0:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/zero-laws-final"
bash tools/check-local-ci.sh`. Its inventory, stages and result are retained in
verification/zero-laws-ci-2026-10-13.log and _build/local-ci-logs/zero-laws-ci.log.
Shell syntax, actionlint and git diff --check pass. Remote CI is not inspected.
This proof-progress checkpoint follows 9ef8568 and is authorized for ordinary
commit and push; it is not a completed Theorem 7.

Twelve of nineteen relational observation laws are now proved. Seven remain:
addition/successor and multiplication/successor equations, and the five order
propagation laws. The full 31-argument observation assembly, negative ground
faithfulness, four-constructor bounded invariant, and independent functional
deduction preservation remain open. No new axioms or admissions were added.

Exact next goal: uniformly for q>0, construct
`Pi u:Fq. delta(u) -> Pi v:Fq. delta(v) ->
Neg(R0 (add (s u) v) (s (add u v)))`, for the capped successor and addition.
Use guarded_finite_realized with a rank-two binary family, reduce selector
branches using capped_successor_action and capped_addition_action, and prove
the resulting capped index equation. The analogous multiplication step must
handle a zero right factor separately when reasoning about saturation.

Next command after implementing the next law (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short
--no-buffer theories/DirectRFunctionalAudit.vo`.

## Historical continuation: operation congruence, following bc5cee0

Request: proceed proving Theorem 7, commit and push. Starting HEAD was
bc5cee044179b6adbd3ec5ed6415d560886fffd5 on main. The user's untracked logs/
is preserved and excluded from the commit. Theorem 7 is NOT complete.

The complete baseline local CI driver exited 0, including pristine upstream:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/operation-congruence-baseline"
bash tools/check-local-ci.sh`, with the documented local bin directory on PATH.
Raw output: _build/local-ci-logs/operation-congruence-baseline.log.

New checked results: FiniteUnaryCongruence.successor_congruence_realized,
FiniteBinaryCongruence.addition_congruence_realized and
FiniteBinaryCongruence.multiplication_congruence_realized, uniformly for q>0.
Each returns Realizes of the expanded, interleaved domain-guard telescope.
The unary conclusion is Neg(R0 (s u) (s v)) under Neg(R0 u v).
The binary conclusion is Neg(R0 (op u v) (op u' v')) under both equality
premises; all four objects have their own immediately following delta guard.
R0 is the finite equality relation, s/op the existing capped selector tables.
Explicit beta equivalences and rank-five formation retain all annotations.

The generic proofs require typed operations and admitted outputs on every
selector tuple. Existing delta_successor/delta_addition/delta_multiplication
discharge these premises, without an assumed equality-congruence theorem.
RelationTables.boolean_premises_realized handles Boolean premises with an
arbitrary rank-one negative conclusion; it does not assert general ex falso.

Incremental commands (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short
--no-buffer theories/DirectRFiniteUnaryCongruence.vo` and the analogous
DirectRFiniteBinaryCongruence.vo target. Both compiled; exit-0 output is in
_build/local-ci-logs/unary-operation-congruence-2.log and
binary-operation-congruence-2.log. First attempts retained in numbered logs:
the unary conversion needed lift_closed_zero normalization before conversion;
the binary operation type needed an explicit closed_term scope annotation.
Neither failure was bypassed or admitted.

Nine of nineteen relational observation certificates are now proved. Ten
remain: five arithmetic equations and five order-propagation laws. The entire
31-argument observation, negative ground faithfulness, four-constructor bounded
invariant, and independent functional deduction preservation remain unfinished.

Exact next goal: the finite addition-zero certificate, uniformly for q>0:
`Pi u:Fq. delta(u) -> Neg(R0 (add z u) u)` with z=point q 0 and
add=capped_addition q. Reduce each admitted selector branch with the checked
binary table action, prove the bounded native index equality, and construct
the PTS negative equality inhabitant before closing the guarded telescope.

Next command after implementing that certificate (documented OPAMROOT/PATH):
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short
--no-buffer theories/DirectRFunctionalAudit.vo`.

Fresh isolated full build exited 0, including the legacy examples:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- timeout 300 dune build \
  --build-dir /tmp/pts-rk-operation-congruence.25yLVh --display=short --no-buffer
```

All 156 assumption reports are closed (48 in the functional audit). Exact
public theorem types, expanded definitions and output are retained in
verification/operation-congruence-full-2026-10-13.log. Raw output:
_build/local-ci-logs/operation-congruence-full.log.
The complete updated local CI driver also exited 0, including pristine upstream:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/operation-congruence-final"
bash tools/check-local-ci.sh`. Output is retained in
verification/operation-congruence-ci-2026-10-13.log and raw
_build/local-ci-logs/operation-congruence-ci.log. Shell syntax, actionlint and
git diff --check pass. Remote CI has not been inspected.
This checked proof-progress checkpoint follows bc5cee0 and is authorized for
ordinary commit and push. It does not claim an unconditional Theorem 7.

## Historical continuation: finite transitivity and congruence, following 5b8e676

Request: proceed proving Theorem 7, commit and push. Starting HEAD is
5b8e676f288aa6c12e0c61d7e6b60cab5692754d on main. Only the user's untracked
logs/ was present; it is preserved. Theorem 7 is still NOT complete.

The baseline complete local CI driver exited 0, including pristine upstream:
`DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/theorem7-transitive-baseline"
bash tools/check-local-ci.sh` (with the documented local bin directory on PATH).
Log: _build/local-ci-logs/theorem7-transitive-baseline.log.

New checked modules:
- DirectRGuardedFiniteLaws opens arbitrary finite telescopes of interleaved
  selector/domain binders, then uses the already checked rank-three finite
  eliminator. guarded_typed proves exact rank r for arity zero and max(5,r)
  otherwise. No membership certificate is eliminated into the rank-five
  guard telescope; all guards are opened first.
- DirectRFiniteTransitivity constructs closed equality- and order-transitivity
  certificates for every q>0. Their PUBLIC types are the expanded three-object
  telescopes, with a domain guard immediately after each object.
- DirectRFiniteCongruence proves equality transport in both arguments of every
  finite Boolean relation, hence the observation's order-congruence certificate.
  Its public type is the expanded four-object interleaved telescope.

All three laws are original PTS inhabitants. Explicit beta equivalences and
rank-five formation proofs connect the generic curried families to those
expanded statements; annotations are retained. Boolean Horn branch validity
is discharged using native equality/transitivity only as numerical side facts.
There is no new axiom, admission, cumulativity or unchecked cast.

Incremental commands used the documented opam switch and
`timeout 90 dune build --display=short --no-buffer TARGET.vo`.
Exit-0 logs under _build/local-ci-logs: guarded-telescope-5.log,
finite-transitivity-4.log, finite-congruence-2.log, finite-laws-audit-2.log.
The extended functional audit has 38 closed assumption reports.
Earlier numbered compiler failures remain available: fixed renaming scope,
dependent empty-index elimination, list-predicate inference, a bracket typo,
and a rank-max arithmetic normalization step. None was admitted.
The updated complete local CI driver exited 0, including the three added
stages and pristine upstream; raw log _build/local-ci-logs/finite-laws-ci-driver.log.
Fresh isolated FULL build exited 0, including every legacy example:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- timeout 300 dune build \
  --build-dir /tmp/pts-rk-finite-laws.uRpSAn --display=short --no-buffer
```

All 146 assumption reports are closed (38 in the functional audit). Exact
public types, expanded definitions and full output are retained in
verification/finite-laws-full-2026-10-13.log; raw log:
_build/local-ci-logs/finite-laws-fresh-full.log. The local CI inventory, stage
statuses and exit result are in verification/finite-laws-ci-2026-10-13.log.
Shell syntax, actionlint and git diff --check pass. This checkpoint is committed
as proof progress after 5b8e676; it does not claim remote CI success or a complete
Theorem 7. Ordinary commit and push are authorized by the current request.

Exact next proof goal: for every q>0, construct the closed successor-congruence
certificate
`Pi u:Fq. delta(u) -> Pi v:Fq. delta(v) ->
Neg(R0 u v) -> Neg(R0 (s u) (s v))`,
where R0 is the equality test and s is capped_successor q. Use the generic
guarded_finite_realized theorem and capped table beta action. Then handle
addition/multiplication congruence analogously using binary_table_action.

Six of the nineteen relational observation certificates are now proved:
equality reflexivity/symmetry/transitivity, order reflexivity/transitivity,
and order congruence. Thirteen remain: three operation congruences, five
arithmetic equations and five order-propagation laws. Assemble the entire
observation telescope before claiming no_back or negative ground faithfulness.
The four-constructor invariant and independent functional deduction preservation
also remain open. This checkpoint is NOT an unconditional Theorem 7.

Next build command after implementing the next law (with documented OPAMROOT/PATH):

```sh
opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short --no-buffer \
  theories/DirectRFunctionalAudit.vo
```

## CI continuation: supplied logs_103946087456

The supplied job reports a runner shutdown, exit 143, not a Rocq diagnostic or
elapsed workflow/stage limit. See CI-103946087456.md for exact evidence.
Locally reproduced a separate memory bottleneck in the legacy examples:
reifying the entire generated syntax in Ltac grew to approximately 19 GB.
The compact-witness repair preserves the generator, statements and fuel 65536.
DirectRTests now compiles (exit 0), with all nine assumption reports closed;
log `_build/local-ci-logs/ci-examples-compact.log`. A fuel-256 experiment timed
out (124) and was reverted. The original high-memory attempt was manually
terminated (143). A fresh full build in /tmp/pts-rk-ci-repaired.sh2eTQ exited 0;
the complete local CI driver also exited 0, including pristine upstream and
all legacy examples. Exact output is in verification/ci-repaired-full-2026-10-13.log
and _build/local-ci-logs/ci-repaired-driver.log. CI repair commit 61330e3 was
pushed to origin/main. No subsequent remote CI outcome has been inspected.
The driver now records TERM/INT interruptions without weakening any check.
Signal-injection test, shell syntax and actionlint passed.

## Current request and exact targets

Active focus (latest user request): continue Theorem 7, commit and push
the checked proof progress. See the current continuation at the top.
Theorem 7 is NOT complete. Theorem 4 remains proved as Theorem4.theorem4.
The PTS set model is not being advanced in this continuation.

The authoritative new reference is
`PTS_rk_interprets_Tarski_Mostowski_Robinson_arithmetic_R_harmonized.tex`.

- Theorem 4, label `main`: the unary-domain relational interpretation.
- Theorem 7, label `thm:direct-R`: the arithmetic-expression functional interpretation.
- Both include all-index axiom realization, preservation of independently
  defined classical source deductions, ground proofs/refutations, and
  nonfaithfulness on arbitrary sentences.
- The unary Theorem 4 is proved. The functional Theorem 7 remains open.
  The old `Kernel.Theorem5Target` is only the functional axiom-witness component.
- The latest user additionally requests the paper's PTS set model using
  rocq-archive/zfc, after the arithmetic work, with separate commits/pushes.
  This supersedes the older exclusion of set models. Its soundness has NOT
  been formalized. The paper states ZF+GCH, not unconditional ZFC.
- Ordinary commits/pushes are authorized. No gh, publish.sh, force-push, or merge.

## Checkout and environment

The earlier continuation started at main commit
`04cf08bb26def30c100ebb1c6cceca6a4de75138` (complete unary relational Theorem 4).
Only the existing untracked logs/ directory was present. It was preserved.

Arithmetic progress checkpoint on main: `a16646b`
(`Prove ground arithmetic and add harmonized unary foundations`), pushed.
It follows `b6fa20660860258717637426605353e0bf3e38e5`.
Inspect git log/status for subsequent model work; do not reset.
User's new harmonized TeX is preserved, including its
pre-existing trailing space at line 287. Downloaded `logs/` remain untouched
and untracked.

Installed local environment: `$HOME/.local/share/pts-rk-ci`; opam root
`opam/`, switch `pts-rk-ci`, binaries `bin/`, native ARM GMP `native/`.
OCaml 4.14.2, Rocq core/runtime 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
Dune 3.23.1, opam 2.6.1, actionlint 1.7.12. GNU timeout is available.
The pristine upstream requires Rocq 9.2's Create Rewrite HintDb.

## Actually compiled

### Historical functional checkpoint through 5b8e676

The current continuation at the top supersedes this checkpoint's remaining-law
counts and next goal; its commands and logs below remain historical evidence.

The target is the harmonized thm:direct-R, using the EXISTING Codes.Domain,
Good, Equality, Order and four expression constructors, not Unary.Domain or a
graph interpretation. Its desired closed preservation judgment is
`exists p, @typ nat RankSorts 0 ε p (FirstOrder.sentence_translation A)` for
each independent classical functional derivation of A. FirstOrder currently
has syntax/translation but no complete independent deduction judgment.

New checked modules:
- DirectRFunctionalTerms: arbitrary open-term typing, Good closure and observed
  closure; every closed expression has a genuine EqAt proof to its numerical
  value's numeral. This covers arbitrary nested addition and multiplication.
  True ground equations and comparisons now have PTS inhabitants for arbitrary
  closed source terms, not just numeral instances.
- DirectRFunctionalLogic: fixed, fully annotated equality/order stability
  certificates over the entire 31-argument arithmetic observation telescope;
  contextual double-negation elimination for the two atomic relations.
- DirectRBinaryTables: generic binary selector tables, their typing and uniform
  beta action; capped addition and multiplication as specializations.
- DirectRBinaryObservations: positive delta closure for every bounded binary
  table, by two rank-three motive eliminations, then abstraction over the
  target membership continuation. Capped addition/multiplication closure are
  checked corollaries. No selector-canonicity assumption is used.
- DirectRRelationTables: generic equality/order test matrices, rank-one result
  typing and point computation, plus PTS proofs of true negative entries and
  contradiction from false negative entries. The latest continuation also
  compiles arbitrary Boolean Horn branches to PTS inhabitants, uniformly in
  the number of premises, and proves their exact rank (two or three).
- DirectRFiniteLawElimination: exact lifting via J2 -> A, and elimination of
  arbitrarily many positively admitted selector arguments into a law of rank
  at most three. The branch premise ranges over all bounded tuples, uniformly
  in arity. This is derived from original typing, not assumed cumulativity.
- DirectRFunctionalFiniteLaws: closed guarded equality- and order-reflexivity
  and equality-symmetry certificates, uniform in every positive selector arity.
  Symmetry eliminates two positively admitted arguments; its false-premise
  branch constructs only a negative conclusion. The other 16
  relational certificates of the functional observation are not yet proved.

Baseline build of DirectR.vo and DirectRRelationalAudit.vo exited 0; log
_build/local-ci-logs/theorem7-baseline.log. Incremental commands use
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short --no-buffer`
with the corresponding module target. Exit-0 logs: functional-terms-build-2.log,
functional-ground-build-2.log, functional-logic-build-1.log,
binary-tables-build-7.log, binary-observations-build-2.log,
relation-tables-build-3.log, finite-law-elimination-build-4.log,
functional-finite-laws-build-1.log. All are under
_build/local-ci-logs; earlier failed attempts remain available. Fixed actual
errors in rename/substitution normalization, intermediate beta terms, and
missing imports; no proof was admitted or assumed.

Exact remaining proof obligations:
1. Apply the checked relation tables and arbitrary-arity finite-law eliminator
   to the remaining 16 guarded relational laws. Prove their arithmetic-expression
   branch computation and assemble all 23 proof arguments of the functional
   finite observation, then derive functional no_back and unequal-numeral
   refutations. Reflexivity and symmetry are done; the next law is guarded
   equality transitivity (then order transitivity using the same construction).
2. Prove the four-constructor positive invariant with functional CaseAt, using
   transferred guarded laws. Unary bounded_case is NOT this theorem.
3. Complete independent functional deduction preservation, formula stability
   and guarded equality transport. Connect source countermodel soundness and
   ground negative refutations; assemble an unconditional final Theorem 7.
Do not substitute Theorem4.theorem4 or the conditional generator record.

Earlier isolated proof build exited 0 (before symmetry/Horn branch additions):

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- timeout 300 dune build \
  --build-dir /tmp/pts-rk-functional-final.ILSavU --display=short --no-buffer \
  theories/DirectRFunctionalAudit.vo theories/DirectRRelationalAudit.vo \
  theories/DirectRUnaryAudit.vo theories/DirectR.vo \
  theories/DirectRArithmetic.vo models/SetFunctions.vo
```

All 25 new functional Print Assumptions queries are closed under the global
context; 124 closed reports including the previous audits. Theorem 4 rebuilt
successfully. Exact public types and output are retained in
verification/functional-progress-2026-10-13.log, raw log
_build/local-ci-logs/functional-progress-fresh.log. The earlier isolated build
in /tmp/pts-rk-functional-check.LbunRw also exited 0 before the last finite-law
extensions; its raw log is functional-foundations-fresh.log.
No final unconditional Theorem 7 type exists yet; this audit explicitly says so.

Earlier full-suite command `opam exec --switch=pts-rk-ci -- timeout 120 dune build
--build-dir /tmp/pts-rk-functional-final.ILSavU --display=short --no-buffer`
exited 124 in unchanged DirectRTests. Raw log:
_build/local-ci-logs/functional-progress-full.log; tracked transcript:
verification/functional-progress-full-2026-10-13.log. This is not a successful
full-suite build or remote CI run. Whitespace, shell syntax and actionlint checks
pass. Eight new CI stages cover the added proof
modules; no stage or timeout was removed or weakened. This earlier timeout is
superseded by the successful full build after the compact-witness CI repair;
retain it as historical evidence, not the current result. The functional work
is a separate progress commit after 61330e3, NOT a completed Theorem 7.
Existing untracked logs/ is untouched.

Exact next build command, after implementing the next guarded finite law:

```sh
opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short --no-buffer \
  theories/DirectRFunctionalFiniteLaws.vo theories/DirectRFunctionalAudit.vo
```

The next exact goal is a closed proof of the telescope
`Pi u:Fq. delta(u) -> Pi v:Fq. delta(v) -> Pi w:Fq. delta(w) ->
Neg(R0 u v) -> Neg(R0 v w) -> Neg(R0 u w)` for R0 = equality_test q.
Use delta_eliminate_arguments at rank three, relation-table point computation,
and boolean_horn_realized. The analogous order law uses Nat.leb transitivity.
Do not rely on the unchecked named generator or on a finite successful example.

Latest checked public certificate:
`forall q, 0 < q -> Realizes (FunctionalFiniteLaws.symmetry_type q Nat.eqb)`.
Here symmetry_type is the exact interleaved telescope
`Pi u:Fq. delta(u) -> Pi v:Fq. delta(v) -> Neg(R0 u v) -> Neg(R0 v u)`.
Realizes means `exists p, @typ nat RankSorts 0 ε p T`, not a checker predicate.
Incremental symmetry build exited 0 in functional-symmetry-12.log; the extended
audit (including arbitrary Boolean Horn branches) exited 0 in
functional-horn-1.log. Earlier numbered failures are retained in
_build/local-ci-logs and were repaired, not admitted.

Final fresh FULL build of this functional progress checkpoint exited 0:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- timeout 300 dune build \
  --build-dir /tmp/pts-rk-theorem7-progress.cWBK5u --display=short --no-buffer
```

All modules, including DirectRTests, compiled. The functional audit has 29
closed assumption reports; the whole fresh build has 137. Public types and
full output are retained in verification/theorem7-progress-full-2026-10-13.log
(raw: _build/local-ci-logs/theorem7-progress-full.log).
The preceding complete local CI driver's inventory/stages/result are retained
in verification/ci-repaired-stages-2026-10-13.log; every stage passed, including
pristine upstream. Shell syntax, actionlint and git diff --check also pass.
No new assumptions, admissions or checking bypasses were introduced.
This is verified proof progress, not an unconditional final Theorem 7.

### Complete unary relational Theorem 4, following a13b0d6

DirectRRelationalTranslation now proves implication/universal introduction,
typed and admitted environment extension, arbitrary-formula stability, classical
DNE and equality reflexivity. Stability includes arbitrary nesting of guarded
quantifiers. DirectRLogic adds double-negation mapping using actual PTS terms.

DirectRRelationalEquality proves term and binary-operation congruence, atomic
equality/order transport, arbitrary-formula transport and equality replacement.
The quantifier case compares the same bound object and Good guard; it does NOT
assume that Good is invariant under raw E. Binary congruence uses fully annotated
lambda abstraction and beta conversion only.

DirectRRelationalDeduction proves preservation by induction on the INDEPENDENT
Relational.derives judgment, with all nine constructors handled. Its closed
corollary is exactly:

    forall A : Relational.formula 0, Relational.derives [] A ->
      exists p, @typ nat RankSorts 0 ε p (RelationalTranslation.sentence A).

DirectRRelationalCountermodel connects the existing option-nat SOURCE model to
the independent calculus. Atomic decidability and formula stability prove
classical-rule soundness constructively, without any native classical axiom.
It proves non-derivability of forall x, x <= x. This is not a PTS set model.

DirectRTheorem4 combines all-index source axiom realization, full deduction
preservation, proofs/refutations for every closed source atom, and nonfaithfulness.
The latter uses Unary.rho_realized and source order_reflexivity_underivable.
Theorem4.theorem4 is a conjunction of those unconditional conclusions in original
typ, not a record hypothesizing preservation or a finite test collection.

Baseline: `opam exec --switch=pts-rk-ci -- dune build --display=short --no-buffer
theories/DirectRRelationalAudit.vo`, exit 0, relational-intro-baseline.log.
Incremental commands use `opam exec --switch=pts-rk-ci -- timeout 90 dune build
--display=short --no-buffer` with the corresponding module target. Successful
logs under _build/local-ci-logs: relational-intro-build-2.log,
relational-stability-build-4.log, relational-equality-build-6.log,
relational-transport-build-2.log, relational-deduction-build-1.log,
relational-countermodel-build-5.log and theorem4-build-1.log. Earlier failed
attempts are retained: scope inference, explicit intermediate terms, a missing
decidability import and tactic syntax were repaired; no assumption was added.
The final incremental audit reports all 34 assumptions queries closed.

Fresh isolated build exited 0:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- timeout 300 dune build \
  --build-dir /tmp/pts-rk-theorem4-check.CvEbQd --display=short --no-buffer \
  theories/DirectRRelationalAudit.vo theories/DirectRUnaryAudit.vo \
  theories/DirectR.vo theories/DirectRCountermodel.vo \
  theories/DirectRArithmetic.vo models/SetFunctions.vo
```

Log: _build/local-ci-logs/theorem4-fresh.log. All original PTS dependencies and
the complete unary proof rebuilt. There are 99 closed assumption reports across
the audits, including all 34 relational audit queries. The final unconditional
theorem types and the compiler transcript are retained in
verification/theorem4-2026-10-13.log. No full-suite or remote-CI success is inferred
from this proof-target build.

Full-suite command `opam exec --switch=pts-rk-ci -- timeout 120 dune build
--build-dir /tmp/pts-rk-theorem4-check.CvEbQd --display=short --no-buffer`
exited 124 in unchanged DirectRTests. Raw log: _build/local-ci-logs/theorem4-full.log;
tracked transcript: verification/theorem4-full-2026-10-13.log. This repeats the
previous legacy-examples timeout, not a compiler error in the new proof. No CI
stage or timeout was removed or weakened; four new stages cover equality,
deduction, source countermodel and the final theorem. Shell syntax, actionlint,
and git diff --check pass. The user logs/ directory remains untouched/untracked.
The changes are prepared for the authorized ordinary commit/push with message
`Prove unary relational Theorem 4`.

Next exact command (recheck the final theorem and transitive assumptions):

```sh
opam exec --switch=pts-rk-ci -- dune build --display=short --no-buffer \
  theories/DirectRRelationalAudit.vo
```

No unary Theorem 4 proof goal remains. Preserve the separate functional target
and model work; do not silently relabel either as completed by this theorem.

### Independent relational source and structural translation, following 7e2e736

DirectRRelationalSyntax defines independent scoped terms/formulas and the
relational arithmetic schemes. Its inductive derives judgment has hypothesis,
theory, implication introduction/elimination, universal introduction/elimination,
classical DNE, equality reflexivity and formula equality replacement. Universal
introduction weakens the entire source context, encoding the freshness condition.
No target typing/inhabitation occurs in any derivation constructor. Only Fin is
shared with Syntax. Conjunction/disjunction/existential/iff are classical
abbreviations over falsity/implication/universal with the paper's fixed encoding.

DirectRRelationalTranslation proves term/formula renaming and substitution,
including instantiate_translation at binders; exact formula ranks; original
PTS term typing and Good evidence under typed/admitted environments; closed
source term translation to unary numerals; implication and guarded universal
elimination. DirectRRelationalAxioms proves the original typing judgment for
the structural translation of every independently stated source axiom, in
arbitrary target contexts. DirectRRelationalGround proves true/false equality,
order, addition-graph and multiplication-graph source atoms for ALL closed
source terms, not just a separate family of target-side atom definitions.

Baseline command `opam exec --switch=pts-rk-ci -- dune build --display=short
 --no-buffer theories/DirectRUnaryAudit.vo` exited 0, log
_build/local-ci-logs/relational-source-baseline.log. Incremental commands used
`opam exec --switch=pts-rk-ci -- timeout 90 dune build --display=short --no-buffer`
with targets DirectRRelationalSyntax.vo (relational-syntax-build-3.log),
DirectRRelationalTranslation.vo (relational-translation-build-2.log and -3.log),
DirectRRelationalGround.vo (relational-ground-build-1.log),
DirectRRelationalAxioms.vo (relational-axioms-build-1.log), and both last targets
(relational-rules-build-1.log): all exit 0. Logs remain in _build/local-ci-logs.
Earlier failed scripts (source context weakening and an omitted falsity branch
in a structural induction) remain recorded and were repaired without admissions.

Fresh isolated build exited 0: `opam exec --switch=pts-rk-ci -- timeout 300
 dune build --build-dir /tmp/pts-rk-source-check.Vath3i --display=short --no-buffer
 theories/DirectRRelationalAudit.vo theories/DirectRUnaryAudit.vo theories/DirectR.vo
 theories/DirectRCountermodel.vo theories/DirectRArithmetic.vo models/SetFunctions.vo`.
All original PTS dependencies and new source/translation modules rebuilt.
All 21 new Print Assumptions queries are Closed under the global context,
with 86 closed reports including prior audits. The exact derivation definition,
public theorem types and compiler transcript are tracked in
`verification/relational-source-2026-10-13.log`; local copy is
`_build/local-ci-logs/relational-source-fresh.log`. Whitespace, shell syntax,
and actionlint checks passed. Five dedicated source/translation CI stages
were added; no existing stage or timeout was removed or weakened.
Full build `opam exec --switch=pts-rk-ci -- timeout 120 dune build
 --build-dir /tmp/pts-rk-source-check.Vath3i --display=short --no-buffer`
exited 124 in unchanged DirectRTests. Exact output is retained in
`verification/relational-source-full-2026-10-13.log` and the local
`_build/local-ci-logs/relational-source-full.log`. No full green build or
remote CI success is claimed. User logs/ and the TeX were left untouched.

Theorem 4 remains INCOMPLETE. Exact next goal: formula stability and formula
equality transport for two typed/admitted environments whose corresponding
terms are E-related. Use these to preserve classical DNE and equality_replace;
prove introduction rules and induction on Relational.derives. Then prove
semantic soundness of that independent system in the existing source
countermodel to establish non-derivability of universal reflexivity. No final
deduction-preservation theorem or source non-derivability theorem is yet present.
Next command: `opam exec --switch=pts-rk-ci -- dune build --display=short
 --no-buffer theories/DirectRRelationalAudit.vo`.

### All relational axiom schemes, following cf105ba

- DirectRUnaryBounded proves both directions of bounded order for arbitrary
  admitted objects, packages the negative biconditional, and proves R4_realized
  for every cutoff. It retains the Good guard. The converse uses stable O;
  the forward large branch is refuted by the checked no_back witness.
- DirectRUnaryEvaluation now proves fully annotated Church normal forms and
  the all-index beta equations Add nu_m nu_n =beta nu_(m+n), and
  Mul nu_m nu_n =beta nu_(m*n). No eta equality or altered annotation is used.
- DirectRUnaryArithmetic proves relational R1/R2 for arbitrary admitted third
  arguments. Ground addition/multiplication atoms have witnesses when the
  external numerical equation is true, and internal Neg witnesses when false.
- all_axioms_realized covers every relational axiom index (R3 carries its
  specified distinctness side condition). The audit restates it as
  `forall a, exists p, @typ nat RankSorts 0 epsilon p (axiom_translation a)`.
  This is axiom realization, NOT preservation of an independent proof system,
  and NOT the functional Kernel.Theorem5Target.

Baseline: `opam exec --switch=pts-rk-ci -- dune build --display=short
 --no-buffer theories/DirectRUnaryAudit.vo`, exit 0, r4-baseline.log.
Meaningful incremental builds (same command with `timeout 90` before dune):
DirectRUnaryBounded.vo (r4-build-3.log), DirectRUnaryEvaluation.vo
(unary-arithmetic-build-2.log and unary-arithmetic-build-4.log), and
DirectRUnaryArithmetic.vo (unary-relational-arithmetic-build-1.log and
unary-relational-arithmetic-build-2.log), all exit 0. Logs are retained in
_build/local-ci-logs. Earlier numbered failures were opaque Neg substitution,
closed-term shift normalization, and a missing parenthesis, all repaired.

Fresh isolated build exited 0: `opam exec --switch=pts-rk-ci -- timeout 300
 dune build --build-dir /tmp/pts-rk-relational-check.8oST6u --display=short
 --no-buffer theories/DirectRUnaryAudit.vo theories/DirectR.vo
 theories/DirectRCountermodel.vo theories/DirectRArithmetic.vo models/SetFunctions.vo`.
Original PTS dependencies, the new proofs and the existing modules rebuilt
successfully. All 13 new Print Assumptions queries report Closed under the
global context; the transcript contains 65 such reports including previous
and set-function audits. Exact types/output are retained in
`verification/unary-relational-2026-10-13.log`, with local working copy
`_build/local-ci-logs/relational-fresh.log`. Whitespace, shell syntax and
actionlint passed. CI now explicitly checks unary bounded-order and arithmetic
before the expanded audit; no old stage or timeout was removed or weakened.
Full build: `opam exec --switch=pts-rk-ci -- timeout 120 dune build
 --build-dir /tmp/pts-rk-relational-check.8oST6u --display=short --no-buffer`
exited 124 while compiling unchanged DirectRTests. Exact output is retained
in `verification/unary-relational-full-2026-10-13.log` and the local
`_build/local-ci-logs/relational-full.log`. No full green build or remote CI
success is claimed. Existing user logs/ and the TeX were left untouched.

Theorem 4 remains incomplete. Exact next goal: define an independent scoped
classical deduction system for the relational signature {0,S,=,<=,A,M}, with
its own axiom schemes and rules; define its structural guarded negative
translation and prove substitution, formula stability, admitted equality
replacement and rule preservation. Do not define source provability as target
inhabitation. Connect the existing source countermodel to semantic soundness
of that system to establish non-derivability of universal reflexivity. Ground
source terms must also be connected structurally to the checked numeral atoms.
DirectRFirstOrder is the old functional-signature translation (binary + and *
terms, no ternary A/M formulas); do not mistake it for the relational system
or silently reuse its distinct Codes.Domain in the unary interpretation.
Next command: `opam exec --switch=pts-rk-ci -- dune build --display=short
 --no-buffer theories/DirectRUnaryAudit.vo`.

### Upward closure and numeral evaluation, following b89cdd2

DirectRFiniteUp.upward_realized now constructs the uniform closed judgment
`Realizes (Pi u:F_(c+1). delta_(c+1)(u) -> Neg(Pu) -> Neg(P(su)))`.
Its exact-rank-three motive is eliminated using the positive delta predicate.
Below the cap an inhabitant of Top supplies the contradiction; at the cap
the negative implication is identity. No positive ex-falso is used.
DirectRUnaryEvaluation.numeral_evaluation proves the actual unary numeral
fold into arbitrary scoped arguments, and finite_numeral_evaluation connects
it to the capped selector at min(k,c), uniformly in both external indices.
Fixed open zero/successor beta schemas are instantiated by the original
replace_equiv lemma; this is not finite testing or annotation erasure.
Incremental commands: `opam exec --switch=pts-rk-ci -- dune build
 --display=short --no-buffer theories/DirectRFiniteUp.vo`, then the same
command with DirectRUnaryEvaluation.vo and DirectRSeparation.vo.
Logs `_build/local-ci-logs/up-build-2.log`, `unary-evaluation-build-1.log`,
`separation-build-2.log` exited 0. The last includes exact observation
predicate d0/ds/Up wrappers and a checked fixed order eliminator.
The first Up attempt needed an explicit scope; the first observation wrapper
needed an explicit rank-one formation proof. Both failures are retained.
Specializing the complete telescope with unstructured substitutions was
interrupted (exit 130); a repeat timed out at 45 seconds (exit 124).
Logs `separation-build-3.log` and `separation-build-4.log` preserve these.
Compact intermediate observation types now solve the telescope specialization;
the new replace_observation lemma keeps closed encodings opaque. Remaining
compiler errors were scope/rank inference and selector substitution, repaired
without changing a statement. `separation-build-7.log`, `separation-build-10.log`
and `separation-build-11.log` exited 0 (60-second command limit).
Separation.no_back_realized is now unconditional for every external k:
`exists p, @typ nat RankSorts 0 ε p
 (Neg (Unary.O (Unary.numeral (S k)) (Unary.numeral k)))`.
Separation.ground_order_refutation handles every j<i, and
Separation.R3_realized handles every i<>j with an internal E refutation.
No hypothesis asserts canonicality of raw selectors or the desired theorem.
Theorem 4 remains incomplete. Exact next goal: both directions of relational
R4, combining bounded_case_realized with no_back_in_context to eliminate
the large branch, and the existing ground comparison for the converse.
Also remaining: unary arithmetic beta equations and relational R1/R2,
ground ternary atoms, and independent classical deduction preservation.
Fresh isolated build exited 0:
`opam exec --switch=pts-rk-ci -- timeout 300 dune build
 --build-dir /tmp/pts-rk-separation-check.Xxoo9H --display=short --no-buffer
 theories/DirectRUnaryAudit.vo theories/DirectR.vo
 theories/DirectRCountermodel.vo theories/DirectRArithmetic.vo models/SetFunctions.vo`.
The original PTS dependencies were rebuilt from source alongside the new
proofs and existing interpretation modules. All ten new Print Assumptions
queries are closed under the global context (52 closed reports in total,
including existing modules). Exact types and compiler output:
`verification/unary-separation-2026-10-13.log`; working copy:
`_build/local-ci-logs/separation-fresh.log`.
Whitespace, shell syntax and actionlint checks passed. Dedicated finite-Up,
unary-evaluation and separation stages were added without removing old checks.
The subsequent full build exited 124 after 120 seconds in unchanged
DirectRTests: `opam exec --switch=pts-rk-ci -- timeout 120 dune build
 --build-dir /tmp/pts-rk-separation-check.Xxoo9H --display=short --no-buffer`.
Output is retained in `verification/unary-separation-full-2026-10-13.log`
and `_build/local-ci-logs/separation-full.log`. No full green build or remote
CI result is claimed. Only the pre-existing user logs/ directory remains
outside the intended commit; no user changes were modified.
Next command: `opam exec --switch=pts-rk-ci -- dune build --display=short
 --no-buffer theories/DirectRSeparation.vo`.

### Positive finite-observation certificates, following 8b49750

DirectRPositive now derives finite positive argument telescopes, their
introduction/application and rank bounds, and positive finite membership
formation/introduction/elimination. Context-extension transport is proved
from original PTS weakening; no semantic validity assumption is introduced.
DirectRFiniteObservations instantiates exactly
`delta q u = Pi Q:(Fq -> U3). Q e0 -> ... -> Q e(q-1) -> Q u`.
Checked: rank-4 formation for q>0, every point certificate, arbitrary rank-3
predicate elimination, and capped-successor preservation. In particular:
`delta_step_realized : forall q, 0 < q -> Realizes
 (Pi u:Fq. delta q u -> delta q (capped_successor q u))`.
This is an actual existential original-PTS term, not a host arithmetic fact.
No assertion that arbitrary raw selectors are canonical is used.

Incremental builds: `_build/local-ci-logs/positive-arrows-build-2.log`
and `positive-arrows-build-4.log`, `positive-arrows-build-5.log`,
`finite-observations-build-1.log`, `finite-observations-build-2.log`,
`finite-observations-build-5.log`, `finite-observations-build-6.log` exited 0.
Failed attempts remain in the same directory: folded Arrows rewrite mismatch,
in_map inference, and two missing scope annotations, all repaired. Final
incremental command was `opam exec --switch=pts-rk-ci -- dune build
 --display=short --no-buffer theories/DirectRUnaryAudit.vo`.
All nine added Print Assumptions queries report Closed under the global context.

Fresh isolated build exited 0, rebuilding original PTS dependencies, unary
audit, DirectR, countermodel, arithmetic and existing SetFunctions. Command:
`opam exec --switch=pts-rk-ci -- timeout 300 dune build
 --build-dir /tmp/pts-rk-positive-check.7cdK7J --display=short --no-buffer
 theories/DirectRUnaryAudit.vo theories/DirectR.vo
 theories/DirectRCountermodel.vo theories/DirectRArithmetic.vo models/SetFunctions.vo`.
Exact transcript, types and assumption output are retained in
`verification/unary-positive-2026-10-13.log` (42 closed-context reports,
including the existing set-function queries).
Shell syntax, actionlint and git diff --check passed.
The subsequent full build, `opam exec --switch=pts-rk-ci -- timeout 120
 dune build --build-dir /tmp/pts-rk-positive-check.7cdK7J --display=short
 --no-buffer`, exited 124 while compiling unchanged DirectRTests. Transcript:
`verification/unary-positive-full-2026-10-13.log`. No full-build or remote
CI success is claimed, and no CI timeout or test was weakened.

At that checkpoint the next proof goal was: build Up(separating_test c) using delta elimination
at the rank-3 motive `Neg(P v) -> Neg(P(s v))`. Finite branches below the cap
use the inhabited Top; the capped branch is identity on Neg Bottom.
Then prove unary numeral evaluation in this observation, specialize O at
these data, and obtain uniform no_back. Remaining Theorem-4 obligations
include unary R1/R2, R3/R4, ground refutations and independent deduction
preservation. Theorem 4 remains incomplete.
Next command: `opam exec --switch=pts-rk-ci -- dune build --display=short
 --no-buffer theories/DirectRUnaryAudit.vo`.

### Comparability and finite-table milestone, following 7c10cc1

- DirectRUnaryAxioms now proves the complete relational comparability scheme
  R5_realized for every external cutoff and arbitrary Good object. It is
  restated as unary_comparability against the original Typing.typ in the audit.
  Both finite and large branches use the checked Case_n theorem; no separation
  premise or native expression-tree induction is assumed.
- DirectRFiniteTables constructs all-arity scoped projection terms and unary
  selector tables. table_typed and table_action prove typing and beta action
  uniformly. The capped table has the exact action i |-> min(i+1,q-1), with
  a checked bound on output indices when q>0.
- The separating test is typed and beta-evaluates to Top below the cap and
  Bottom at the cap. iterate_computation proves every external iteration
  beta-equal to the selector at min(k,c). These are PTS terms and beta proofs,
  not host-logic truth tables or an eta/annotation-erasing bridge.
- Valid selector indices are explicitly bounded in action theorems. No claim
  is made that every raw inhabitant of selector_type q is a selector. The
  required delta_q certificates are still missing, so no_back is NOT proved.

Successful incremental commands (OPAMROOT/PATH as below):
`opam exec --switch=pts-rk-ci -- dune build --display=short --no-buffer theories/DirectRUnaryAxioms.vo`
and the analogous targets DirectRFiniteTables.vo and DirectRUnaryAudit.vo.
Logs (under `_build/local-ci-logs`): `unary-r5-build-3.log`,
`finite-tables-build-3.log`, `finite-tables-action-build-5.log`,
`finite-separating-test-build-2.log`, `unary-comparison-audit.log`, all exit 0.
Earlier numbered logs retain actual failures involving binder/type inference,
list equality rewrites and an implicit nth_indep argument. No axiom/admission
was added. All 27 assumption queries in the expanded unary audit are closed.

Fresh isolated build (exit 0):
`opam exec --switch=pts-rk-ci -- timeout 300 dune build
 --build-dir /tmp/pts-rk-comparison-check.fCSJuL --display=short --no-buffer
 theories/DirectRUnaryAudit.vo theories/DirectR.vo
 theories/DirectRCountermodel.vo theories/DirectRArithmetic.vo
 models/SetFunctions.vo`.
This rebuilt the shared original PTS dependencies and existing DirectR modules
alongside the new proofs. Full transcript, exact theorem types and assumptions:
`verification/unary-comparison-2026-10-13.log`; local copy:
`_build/local-ci-logs/unary-comparison-fresh.log`.
Workflow lint, shell syntax and git diff --check also passed.
The subsequent full build
`opam exec --switch=pts-rk-ci -- timeout 120 dune build
 --build-dir /tmp/pts-rk-comparison-check.fCSJuL --display=short --no-buffer`
returned 124 in the unchanged DirectRTests module. No full green CI claim is
made. Exact output is retained in `_build/local-ci-logs/unary-comparison-full.log`
and `verification/unary-comparison-full-2026-10-13.log`.

At that checkpoint the next goal was: construct delta_q(u) at rank four for q>=2, its point
certificates and closure under capped_successor q, then the Up certificate for
separating_test (q-1). Combine these with unary numeral evaluation to obtain
the uniform original-PTS no_back witness. The finite-table definitions are
intrinsically scoped alternatives to the old named table generator; no bridge
to that unused generator is required for this unary construction.
Next command: `opam exec --switch=pts-rk-ci -- dune build --display=short --no-buffer theories/DirectRUnaryAudit.vo`.

### Previously checked bounded cases

Checked Theorem-4 bounded-case milestone (on top of cfb1dc2):
- Unary equality reflexivity/symmetry/transitivity and congruence for every
  raw endofunction; positive G closure and Good-to-G via exact rank lifting.
- Raw order transitivity, equality-to-order, G-guarded successor order,
  compatibility in both arguments, and equality/order double-negation stability.
- Uniform numeral typing/admission/observation and ground_order_realized for
  every external i <= j (not a finite test).
- Generic rank-ten invariant eliminator cases_from_closure_typed. Its rank-eight
  family, zero proof and G-guarded successor closure are explicit parameters.
  The actual Case_n family now satisfies all those premises uniformly.
- DirectRLogic: all-arity flat disjunction formation, injection and application;
  stability and elimination into stable targets; positive invariant formation
  and introduction. No Bottom elimination into arbitrary positive types.
- DirectRUnary: exact Case_n/Inv_n ranks, zero witnesses, all-cutoff successor
  closure in arbitrary contexts, and the UNCONDITIONAL bounded_case_realized.
  DirectRUnaryAudit restates this as unary_bounded_cases in original typ:

  `forall cutoff, exists p : Term nat 0, @typ nat RankSorts 0 ε p
   (Π Unary.Domain (Codes.Arrow (Unary.admitted Codes.V0)
      (Unary.Case cutoff Codes.V0)))`.

  This quantifies over arbitrary admitted raw objects, not native expression
  trees. It is Lemma `case` of the harmonized note, NOT all of Theorem 4.

Latest successful command (exit 0):
`opam exec --switch=pts-rk-ci -- dune build --display=short --no-buffer theories/DirectRUnary.vo`
with OPAMROOT/PATH as below. Logs: `_build/local-ci-logs/unary-basic-build.log`,
`unary-ground-build.log`, `unary-invariant-build.log`, `unary-case-build.log`,
`unary-case-zero-build.log`. The new generic logic layer first failed on a
nonexistent rename lemma, then on folded syntax, a list-length equation, and
a backwards shift rewrite. Exact failures are retained in
`negative-logic-build.log` and `negative-logic-build-{2,3,4}.log`; the repaired
build is `negative-logic-build-5.log` (exit 0). No failed proof was admitted.

Subsequent successful logs: `negative-stability-build-2.log`,
`negative-elimination-build.log`, `unary-context-build.log`,
`unary-case-step-build-6.log`, `unary-case-closure-build-3.log`,
`unary-bounded-build-2.log`, and `unary-audit-build.log`. Earlier numbered
attempts retain actual syntax/import/unification failures; none was bypassed.
All 15 unary/negative-logic Print Assumptions queries report
`Closed under the global context`, including unary_bounded_cases.

Fresh isolated build (exit 0, no pre-existing compiled objects):
`opam exec --switch=pts-rk-ci -- timeout 300 dune build
 --build-dir /tmp/pts-rk-unary-check.C7rVtH --display=short --no-buffer
 theories/DirectRUnaryAudit.vo theories/DirectR.vo
 theories/DirectRCountermodel.vo theories/DirectRArithmetic.vo
 models/SetFunctions.vo`.
Full output is `_build/local-ci-logs/unary-fresh-build.log`.
The exact fresh-build transcript is also tracked as
`verification/unary-bounded-2026-10-13.log`.
The subsequent full-theory command
`opam exec --switch=pts-rk-ci -- timeout 120 dune build
 --build-dir /tmp/pts-rk-unary-check.C7rVtH --display=short --no-buffer`
returned 124 while compiling the unchanged DirectRTests module. Output is
`_build/local-ci-logs/unary-full-build.log` and the tracked
`verification/unary-full-build-2026-10-13.log`. Thus the fresh proof/module
build passed, but the full legacy example suite is still not verified.
`git diff --check`, actionlint on the existing workflow, and shell syntax
checking of the CI driver passed. Existing user logs/ and TeX were untouched.
The CI driver now explicitly builds negative logic and the unary assumption
audit, without removing any old stage or changing any timeout.

Next proof goal: finite unary selector observation realization and uniform
`no_back_n : O(numeral (S n), numeral n) -> Bottom`. The all-arity selector
API in DirectRStructural is available, but capped-successor tables and delta
closure must still be constructed and typed. Also pending: unary arithmetic
beta equations and relational R1/R2, all-index R3/R4 packaging, ground
refutations, independent source deductions and their preservation. The
functional R1_realized/R2_realized below do not prove unary relational R1/R2.

Next exact baseline command:
`opam exec --switch=pts-rk-ci -- dune build --display=short --no-buffer theories/DirectRUnaryAudit.vo`.

- Original pristine upstream, evaluator and checker soundness.
- DirectRStructural: structural substitution identities; generic dependent
  telescope formation/abstraction/projection; all-arity selector formation,
  typing, typed table application and beta-computation. Bridges connect to
  Codes.selector/Codes.selector_type and the named carrier nSelectorType.
  The named nSelector/operation-table/delta implementations still need bridges.
- DirectRFoundations: all fixed certificates; observed/admitted numerals;
  direct application lemmas for constructor closure, equality/congruence,
  arithmetic equations and order; functional admitted order reflexivity.
- DirectRProofs: uniform ground addition, multiplication and order,
  R1_realized and R2_realized. No legacy certify call remains in this module.
- DirectRGenerated, DirectRFirstOrder, DirectRObligations, DirectR facade,
  and the separate native-Prop arithmetic module. Compiling the definitions
  of generator contracts does NOT prove those contracts.
- DirectRUnary: the revised unary carrier and Church operations, Good,
  negative-test equality, unary-observation G and order, their exact ranks,
  constructor certificates, raw and admitted order reflexivity.
- DirectRCountermodel: the source structure N plus omega satisfies all
  relational and functional arithmetic axiom schemes, but not universal
  order reflexivity. This is NOT a PTS set model. Source non-derivability
  still needs a defined deduction system and its semantic soundness.

Assumption queries for R1_realized, R2_realized and ground_order_typed returned
`Closed under the global context`. The same holds for the checked structural
results and unary rank/closure/reflexivity certificates. No new axiom or
admission was introduced.

## Commands and evidence

Run from repository root:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- dune build --display=short --no-buffer \
  theories/DirectR.vo theories/DirectRUnary.vo \
  theories/DirectRCountermodel.vo theories/DirectRArithmetic.vo
```

Latest module-build transcript: `_build/local-ci-logs/harmonized-modules.log`.
Other exact transcripts: `ground-families-build.log`, `ground-assumptions.log`,
`structural-assumptions.log`, `unary-assumptions.log` in that directory.

`DIRECT_R_STAGE_SECONDS=120 bash tools/check-local-ci.sh` passed stages
01 through 12, including the new dependencies, then found an uninferred scope
in DirectRTests' zero-budget example. Scope is now explicitly 0.
The subsequent command
`opam exec --switch=pts-rk-ci -- timeout 120 dune build --display=short
--no-buffer theories/DirectRTests.vo`
returned 124. Transcript: `_build/local-ci-logs/examples-build.log`.
No full green test/CI run is claimed; the ordinary CI stage limit remains 1200.
An attempted timing probe during dependency rebuilding failed to import the
temporarily absent Foundations object; this is not a new source proof error.
A subsequent probe after rebuilding reached and completed R3_1_0 (about
8 seconds for construction/checking, 2 seconds for Qed), then reached R4_0
without completing it within its 20-second diagnostic limit. The full
120-second examples timeout is still a failure to verify the whole suite.

Tracked build/type/assumption evidence is retained in
verification/harmonized-2026-10-13.log. All 22 final assumption queries there
returned Closed under the global context, with no import or query errors.

Workflow lint and shell syntax were checked. Whitespace checking of agent
changes passes; the supplied TeX's existing trailing space is unchanged.

## Exact remaining work and next commands

First rerun the changed modules using the command above, then inspect the slow
example with (from `_build/default`, after dependencies finish):

```sh
opam exec --switch=pts-rk-ci -- timeout 120 rocq compile -time \
  -R theories PTSrk theories/DirectRTests.v
```

Uniform mathematical goals:
1. Finite unary observations and no_back are now checked in DirectRSeparation,
   with Up and numeral evaluation in their own modules. The unused legacy
   named-generator bridge is not required for the unary interpretation.
2. Unary Theorem 4's uniform invariant and bounded-case proof are now checked.
   The separate functional Theorem 7's four-constructor invariant remains open.
3. All unary relational axiom schemes and ground atoms are checked and now
   connected to independent relational syntax via a structural translation.
4. Unary guarded equality replacement, formula stability, full deduction
   preservation and source non-derivability are now checked. Theorem4.theorem4
   assembles the complete unary statement. Do not redo these obligations.
5. Functional Theorem 7 and the PTS set model remain separate unfinished tasks;
   only advance them on an applicable user request. The legacy DirectRTests
   timeout is a separate full-suite verification issue, not an open Theorem 4
   proof obligation.

Earlier failed approaches: blanket cbv in the symbolic tactic unfolds symbolic
numerals and loses reusable typing evidence. Direct tApp/arrow applications
plus Structural.structural_substitution_in avoid that. Eauto with transitivity
as a global search rule became expensive for multiplication; the successful
proof supplies the two transitivity steps explicitly.

## Subsequent set-model foundations checkpoint

The requested ZFC dependency was inspected at
`ede7126560844c381c2b021003a8dbcb0668ecad`. Its full Makefile failed on the
removed elimtype tactic. A pinned, licensed subset (Sets/Axioms/Cartesian)
is now vendored; one tactic in Cartesian was translated without changing
its statement or assumptions. No gh or publish.sh was used.

`models/SetFunctions.v` constructs the ordinary dependent function set as a
subset of a powerset. Graph abstraction, beta computation, relational
application, uniqueness and empty-fiber emptiness compile, with all five
Print Assumptions reports closed under the global context.

Exact successful command:
`opam exec --switch=pts-rk-ci -- dune build --display=short --no-buffer models/SetFunctions.vo`.
Log: `_build/local-ci-logs/set-functions-build.log`; tracked report under
`verification/set-functions-2026-10-13.log`. CI has a separate model-foundations
dependency stage and still checks every original stage.

This is NOT yet the PTS model or its soundness theorem. Next mathematical
work is the actual countable cardinal/sort-code universes and extensional
decoding, followed by finite-aleph/GCH bounds, coherent coding bijections,
substitution/beta semantics and soundness of the original typing judgment.
See models/README.md. Do not replace those obligations by a record assuming
model laws, or infer Bottom nontriviality merely from the empty-fiber lemma.
