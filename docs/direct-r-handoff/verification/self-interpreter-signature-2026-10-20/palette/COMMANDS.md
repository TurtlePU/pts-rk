# Finite Tarski base palette

Date: 2026-10-20. Working directory: `/Users/akuklev/air/pts-rk`.
Source: `theories/self_interpreter/TarskiPalette.v`, 438 lines.
SHA-256: `cdbb248b125cc2be46e16f6ab25b93c8d12a0c354ceaed2d4eebe61decb87e81`.
Only this new proof module and its evidence are owned by this subtask;
the coordinating agent owns registration, integration and live handoff.

## Constructed interface and boundary

`context k` is an actual recursively constructed original `Ctx`, not a
record postulating that a suitable algebra exists. Its four layers each
have `k+2` declarations, for external indices `0..k+1`:

1. `C_r : U0`;
2. `El_r : C_r -> U_r`;
3. `u_r : C_0`;
4. `w_r : TarskiUniverses.universe_law C_r El_0 u_r`.

`width_exact` proves `width k = 4*(k+2)`. `context_wf` constructs the
original Type-valued well-formedness derivation using explicit declaration
sorts 0, 1, 0 and 2. `context_normal` checks all declarations, including
dependent annotations. `carrier_typed`, `decoder_typed`, `universe_typed`
and `law_typed` give original lookup typings for every `r<=k+1`.
The field builders are literal variables; shape witnesses are provided.
The total selector has a fallback outside this range, with no out-of-range
typing or identity equation promised.

`fill k` is an actual simultaneous substitution sending these variables
to `U_r`, `BrownPalsberg.type_identity r`, `U_r`, and the actual
`TarskiUniverses.identity_universe_witness r`, respectively. `fill_typed`
constructs `Morphisms.TypedSub (context k) G (fill k)` for any target
context G, with no premises. It uses the proved original identity witness
typings, not assumed field-law inhabitants. `fill_carrier`, `fill_decoder`,
`fill_universe` and `fill_law` are exact bounded syntax equations.
`fill_replace` establishes unconditional replacement naturality.

Generic `block`/`fill_block` helpers expose source weakening, variable
lookup, explicit-rank well-formedness, declaration normality, actual typed
instantiation and replacement equations. Each block's signatures depend
only on its earlier base, allowing subsequent product and law layers.
No result-dependent domain strengthening, changed PTS rule, eta,
extensionality assumption, cumulativity or global coherence law is used.

This is a finite BASE signature, not full dependent quotation or coverage.
Products and their law families are added separately. External rank and
literal ceilings must still cover an intended source: source result rank
zero alone does not bound literal labels `U_r`. No such sufficiency or
all-source theorem is inferred from this finite construction.

## Commands and attempts

Fresh absolute build: `/tmp/pts-rk-tarski-palette.9TjYIs`.
Ignored raw evidence: `_build/tarski-palette.IThLxS`.
Each attempt was invoked by
`bash _build/tarski-palette.IThLxS/RUN.sh NN`.
The retained runner is exactly:

```sh
#!/usr/bin/env bash
attempt="$1"
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-tarski-palette.9TjYIs --display=short --no-buffer theories/self_interpreter/TarskiPalette.vo > "_build/tarski-palette.IThLxS/attempt-$attempt.log" 2>&1
build_status=$?
printf '%s\n' "$build_status" > "_build/tarski-palette.IThLxS/attempt-$attempt.exit"
tail -45 "_build/tarski-palette.IThLxS/attempt-$attempt.log"
exit "$build_status"
```

| Attempt | Exit | First outcome |
| --- | --- | --- |
| 01 | 1 | Target not yet registered in Dune. |
| 02 | 0 | Generic block/fill helpers and all four context definitions compiled. |
| 03 | 0 | Original context well-formedness, normal declarations and four lookup endpoints compiled; six closed reports. |
| 04 | 1 | `fill_carrier`: folded final `width` prevented rewriting the generic lift/substitution lemma. |
| 05 | 1 | Temporary `Show` recorded the same obligation. |
| 06 | 1 | Explicit lemma arguments alone did not resolve the folded scope. |
| 07 | 0 | Exposing the definition of `width` fixed matching; actual identity substitution and all remaining endpoints compiled, twelve closed reports. |

All failures are retained, no timeout occurred, no theorem was weakened,
and diagnostic `Show` was removed. The usual logical-loadpath warning was
not suppressed. Successful source-changing attempts reran their assumption
reports; success is not inferred from a cached no-op.

Version command, exit 0 (`versions.log`, `versions.exit`):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune > _build/tarski-palette.IThLxS/versions.log 2>&1
version_status=$?
printf '%s\n' "$version_status" > _build/tarski-palette.IThLxS/versions.exit
```

Actual versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1. Scoped `git diff --check` exits 0; source scan
for admissions, axioms, disabled guard/universe checks and diagnostic Show
has no matches. Source hashing uses `shasum -a 256`.
Recursive kernel, pristine comparison, aggregate audit and full CI are
separate coordinating-agent checks, not claimed by this targeted evidence.

## Assumptions

All twelve endpoint reports are `Closed under the global context`:
`context_wf`, `context_normal`, `carrier_typed`, `decoder_typed`,
`universe_typed`, `law_typed`, `fill_typed`, `fill_carrier`, `fill_decoder`,
`fill_universe`, `fill_law`, and `fill_replace`.
