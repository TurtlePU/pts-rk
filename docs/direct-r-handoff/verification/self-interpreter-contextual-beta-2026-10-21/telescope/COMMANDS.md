# Arbitrary-base dependent telescope closure

Date: 2026-10-21. Working directory: `/Users/akuklev/air/pts-rk`.
Owned source: `theories/self_interpreter/ContextualTelescope.v`, 249 lines.
SHA-256: `1d3e86333e00942a12264d1507bf041e67a23d952b5b3b7d56a4a8faa1021eaa`.
Only this new source and scoped evidence were edited. Coordinator owns Dune,
Audit, prose and live handoff. No existing proof, kernel, Git index or reference
was changed.

## Contract

`telescope n rs` is independent executable data: an outer-to-inner vector of
declaration formation ranks and actual original scoped annotations. `scope`
computes the final width and `context` the actual extended original context.
`formed G D` states only original formation of every annotation in its prefix.
It assumes no coherence, quotation, normalization or identity realization.

`close_term` and `close_type` build the literal nested lambdas and products.
Original closure typing and well-formedness are proved. `close_type_sort` has
the exact recursively computed formation rank `rank rs s`;
`rank_exact` identifies it with max(ceiling rs,s), and `rank_le_iff` characterizes
its upper bounds by the result rank and ALL successor declaration ranks.
`vector_bound` computes a sufficient bound for a supplied finite vector.
Length is separate: `every_vector_bounded` uses the vector's actual length,
and no length bound is inferred from rank alone.

Renaming/substitution of telescopes transforms actual annotations using the
original lifted maps. `formed_replace`, `formed_rename`, `context_sub` and
`context_ren` construct actual original formation and typed maps. No extra
well-formedness guard restricts the original typed-substitution domain.
Closure naturality is literal. Reductions of the supplied body lift under
the fixed telescope. Normality is an EXACT boolean equation and iff: every
annotation and the body must be normal. This is generic closure infrastructure,
not a contextual cast-beta law or a finite field generator by itself.

## Commands and results

Fresh absolute build: `/tmp/pts-rk-contextual-telescope.xlyv7e`.
Ignored raw evidence: `_build/contextual-telescope.uWStHi/`.
Final attempt03 exits 0 with TWENTY-TWO closed own assumption reports.
Independent read-only audit passes without correction.
Recursive kernel checking exits 0. Its loaded inventory contains only the
existing upstream functional-extensionality declaration, with no type-in-type,
unsafe fixpoints or assumed positivity. The new theorem reports are closed.

Each attempt used `bash _build/contextual-telescope.uWStHi/build.sh NN`,
setting the working directory above and exporting:

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-contextual-telescope.xlyv7e --display=short --no-buffer theories/self_interpreter/ContextualTelescope.vo > "_build/contextual-telescope.uWStHi/attempt-${attempt}.log" 2>&1
build_status=$?
printf '%s\n' "$build_status" > "_build/contextual-telescope.uWStHi/attempt-${attempt}.exit"
tail -60 "_build/contextual-telescope.uWStHi/attempt-${attempt}.log"
exit "$build_status"
```

- 01: exit 0, all initial eighteen reports, full closure/morphism core.
- 02: exit 1, new vector-bound proof needed explicit reduction of fold_right
  before native arithmetic could see the maximum.
- 03: exit 0, final twenty-two reports, including exact vector bounds and
  normality iff corollaries. No existing API or theorem premise was changed.

No timeout, admission, weakened statement or disabled check was used. Existing
loadpath-remapping and duplicated-source-path dependency warnings remain visible.

Versions (versions.log/.exit, exit 0):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune > _build/contextual-telescope.uWStHi/versions.log 2>&1
version_status=$?
printf '%s\n' "$version_status" > _build/contextual-telescope.uWStHi/versions.exit
sed -n '1,30p' _build/contextual-telescope.uWStHi/versions.log
exit "$version_status"
```

Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2, Dune 3.23.1.
Recursive kernel command is retained in check.sh with kernel.log/.exit:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-contextual-telescope.xlyv7e/default/theories PTSrk -Q /tmp/pts-rk-contextual-telescope.xlyv7e/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-contextual-telescope.xlyv7e/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.ContextualTelescope > _build/contextual-telescope.uWStHi/kernel.log 2>&1
kernel_status=$?
printf '%s\n' "$kernel_status" > _build/contextual-telescope.uWStHi/kernel.exit
tail -30 _build/contextual-telescope.uWStHi/kernel.log
exit "$kernel_status"
```

Source hash: `shasum -a 256`; scoped git diff --check exits 0. The admission,
axiom and disabled-check scan finds no matches (expected rg exit 1).
Aggregate audit/full CI/pristine checks are coordinator work, not inferred
from targeted compilation.
