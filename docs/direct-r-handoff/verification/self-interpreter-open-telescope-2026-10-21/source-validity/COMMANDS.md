# Computational original source validity

Date: 2026-10-21. Working directory: `/Users/akuklev/air/pts-rk`.
Source: `theories/self_interpreter/SourceValidity.v`, 219 lines.
SHA-256: `943caa76935cc31e2751716894fec2d1c1cc3648e2664c6d1e131ff865c7e196`.
Only this new module and scoped evidence were edited. Coordinator owns
Dune/Audit and shared handoff. No Git/index mutation or frozen-source edit.

## Exact contract

`context_data` contains the original declaration syntax and independent
FullSource derivations of its formation, all in Type. `context_prefix`,
`context_declaration` and `lookup_formation` compute actual source evidence,
retaining original shifts and annotations. `result_formation d c` returns
an actual rank r and FullSource derivation of the literal result type T:U_r.
`result_rank` and `result_type_derivation` expose those projections.

The function is structural on the supplied source derivation. In application,
it recursively obtains formation of the literal function product, then
`product_inversion` strips only outer source conversion constructors to
recover the original domain/codomain formation data. Executable source
substitution produces formation of the literal substituted codomain. No
arbitrary subject-reduction algorithm, erased typing oracle or target
translation is used. Sorts need no exceptional validity branch because the
original axiom is U_r:U_0. A conversion node already contains its target
formation derivation, which is reused directly.

`source_data_iff` covers EXACTLY original typing in original well-formed
contexts. Its reverse direction is a propositional inhabitedness theorem,
not extraction of Type-valued data from Prop. `result_formation_sound`,
`result_type_rank` and `result_rank_agrees` connect the computed output to
the original judgment. `result_rank_independent` allows different source
derivations and different convertible result types for the same term.
The rank is the sort of its TYPE; it is not a literal universe-label bound.
`vm_compute` regressions exercise application, source conversion and
product inversion beneath an explicit conversion constructor.

This module supplies computational source formation for future quotation.
It does not construct target code, internal conversion coherence, a sufficient
target-palette budget, or a full dependent self-interpreter. The original
unguarded sort/variable rules outside well-formed contexts are unchanged;
only this validity interface has the explicit intended wf domain.

## Fresh build and exact attempts

Fresh directories:

```sh
mktemp -d /tmp/pts-rk-source-validity.XXXXXX
mktemp -d _build/source-validity.XXXXXX
```

Resolved build: `/tmp/pts-rk-source-validity.IwqRkC`.
Ignored raw logs: `_build/source-validity.9AO0pn/`.
Each numbered attempt ran `bash _build/source-validity.9AO0pn/build.sh NN`:

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-source-validity.IwqRkC --display=short --no-buffer theories/self_interpreter/SourceValidity.vo > "_build/source-validity.9AO0pn/attempt-${attempt}.log" 2>&1
build_status=$?
printf '%s\n' "$build_status" > "_build/source-validity.9AO0pn/attempt-${attempt}.exit"
tail -65 "_build/source-validity.9AO0pn/attempt-${attempt}.log"
exit "$build_status"
```

| Attempt | Exit | First outcome |
| --- | --- | --- |
| 01 | 1 | New target had not yet been registered in Dune. |
| 02 | 1 | The context extension notation conflicted with sigma notation; replaced it by explicit sigT. |
| 03 | 0 | Computational core compiled, five own closed reports. |
| 04 | 1 | New convenience wrapper appeared before product_inversion; declaration reordered. |
| 05 | 0 | Original coverage and rank agreement compiled, fourteen closed reports. |
| 06 | 0 | Final computational regressions compiled, fifteen closed reports. |

Before actual attempt02, `rg -n 'SourceValidity' theories/self_interpreter/dune && bash _build/source-validity.9AO0pn/build.sh 02`
returned1 while registration was pending; no build ran in that preflight.
No timeout/interruption occurred. Existing loadpath warnings remain in logs.

## Recursive kernel, versions and source checks

`bash _build/source-validity.9AO0pn/check.sh` exited0; exact command:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-source-validity.IwqRkC/default/theories PTSrk -Q /tmp/pts-rk-source-validity.IwqRkC/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-source-validity.IwqRkC/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.SourceValidity > _build/source-validity.9AO0pn/kernel.log 2>&1
kernel_status=$?
printf '%s\n' "$kernel_status" > _build/source-validity.9AO0pn/kernel.exit
tail -25 _build/source-validity.9AO0pn/kernel.log
exit "$kernel_status"
```

All fifteen own transitive reports are CLOSED. The recursive loaded inventory
contains only the unchanged upstream dependent functional-extensionality
entry, with no unsafe fixpoint, type-in-type or assumed positivity.

`bash _build/source-validity.9AO0pn/versions.sh` exited0:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune
```

Rocq9.2.0, Stdlib9.1.0, Equations1.3.2+9.2, OCaml4.14.2, Dune3.23.1.
Versions log/exit and exact retained runner are in the raw directory.
The retained source-check.sh runs scoped git diff --check (exit0) and
rg for forbidden declarations/disabled checks (exit1: no matches); wrapper0.
No admitted proof, new axiom or unsafe cast/check was introduced.

Unchanged dependency SHA-256 values:

- FullSource: `a742200604c651f8344cb6811c28f1bc91f0ecb57e47b18ac30dbd211854f46d`.
- SourceSubstitution: `2198863c000673c55be4ff7c9c76cefbf9e9cd608bca10b51c67380ee11eafa7`.

Hashes/line count use `shasum -a 256` and `wc -l` on the exact source paths.
Final aggregate/pristine comparison and shared state updates are owned by
the coordinator; this record claims only the scoped checks above.
