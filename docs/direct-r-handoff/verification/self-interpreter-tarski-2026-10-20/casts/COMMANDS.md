# Originally typed dependent Tarski casts

Date: 2026-10-20. Source: theories/self_interpreter/TarskiCasts.v.
SHA-256: 9b60a7f46652ea62e87bc648ed7935833906e270b5643814595073c80b788111.
Working directory: /Users/akuklev/air/pts-rk.
Fresh absolute build: /tmp/pts-rk-tarski-casts.GPNiYh.
Raw local-only ignored logs: _build/tarski-casts.ZYuUzT.

## Actual contract

All terms use original annotated Term nat and all judgments use original
Typing.typ with RankSorts. For S,T:Uc, the Leibniz law at predicate level
c+1 has sort U_(c+2). Applying its witness to the motives X |-> S->X and
X |-> X->S, then id_S, constructs both directions of transport. The
motives have the required rank c+1; no same-level predicative symmetry
principle is assumed. Typing is by direct original applications and proved
conversion, not subject expansion.

For c=max(a+1,b), X=Pi x:Ea A.Eb(Bx), Y=Ec(p A B), the law supplies actual
Abs_e(f):Y for f:X and App_e(g,u):Eb(Bu) for g:Y and u:Ea A. All decoder,
product-constructor and argument typings remain explicit. These are local
operations with an explicit typed equality argument, not a premise asserting
successful quotation. TarskiIdentity separately constructs their identity
law witness; ClosedTarskiCasts closes the generic cast programs.

Reflexivity-specialized casts reduce to the literal id_S, and their
applications reduce to the literal input term. The same holds for the
all-rank identity universe witnesses. The cast builders commute exactly
with replacement. Their local normality lemma assumes normal annotations,
normal input and a normal non-lambda proof head. This does not prove global
quotation normality or cancellation of arbitrary neutral transports.

## Every compiler attempt

For each NN below the command was:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-tarski-casts.GPNiYh --display=short --no-buffer theories/self_interpreter/TarskiCasts.vo > _build/tarski-casts.ZYuUzT/attempt-NN.log 2>&1
cast_status=$?
printf '%s\n' "$cast_status" > _build/tarski-casts.ZYuUzT/attempt-NN.exit
tail -n 45 _build/tarski-casts.ZYuUzT/attempt-NN.log
exit "$cast_status"
```

| Attempt | Exit | First result |
| --- | --- | --- |
| 01 | 1 | backward_motive_beta: incomplete replacement/renaming equality. |
| 02 | 1 | Unfolding shift alone did not close that equality. |
| 03 | 1 | Diagnostic Show exposed replacement by successor variables. |
| 04 | 0 | Existing BP.replace_fsucc closes the goal; initial motive theorem checked. |
| 05 | 1 | Developing dependency IndexedEquality: normalb v rewrite absent; dependency owner fixed its nested normality simplification. |
| 06 | 0 | Core casts, law formation and reflexivity computation checked. |
| 07 | 0 | Generic dependent product operations checked. |
| 08 | 0 | Complete source, thirteen own closed assumption reports. |

No timeout occurred. Diagnostic Show was removed. No theorem was weakened,
and no axiom, admission or disabled check was introduced. Logical-loadpath
remapping warnings are retained. The final fresh integrated check, recursive
kernel inventory, pristine comparison, versions and full CI are recorded in
../final-review/COMMANDS.md, not inferred from this incremental compile.
Pinned versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1, opam 2.6.1.

## Own assumption endpoints

motives_typed, type_law_sort, casts_typed, casts_reflexivity,
cast_application_reflexivity, product_law_sort, cast_abs_typed,
cast_app_typed, universe_casts_typed, identity_universe_casts_typed,
identity_universe_casts_recover, casts_replace and neutral_casts_normal.
All thirteen print Closed under the global context in the final source.
Two independent read-only mathematical/API reviews pass.
