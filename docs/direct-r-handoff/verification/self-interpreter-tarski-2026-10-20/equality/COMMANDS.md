# Indexed Leibniz equality: verification evidence

Date: 2026-10-20. Working directory: `/Users/akuklev/air/pts-rk`.
Scope: new `theories/self_interpreter/IndexedEquality.v` only. The coordinating
agent owns Dune registration, aggregate auditing and the live handoff files.

## Contract

All definitions are executable builders of the original annotated
`Syntax.Term nat n`; all typing results use the original `Typing.typ` and
`Ranks.RankSorts`. For `A : U_a` and `u,v : A`,

```
eq_type b A u v = Pi (A -> U_b). P u -> P v
```

has sort `U_(max(a+2,b+1))`. The actual reflexivity term has this equality
type, and the actual application `transport e P p` is typed at `P v` from
the separately supplied original typings of `e`, `P` and `p`. Transport
along reflexivity beta-reduces to the literal input `p`, without typing
premises. A closed polymorphic reflexivity builder is typed, normal and
specializes by beta reduction. Renaming/replacement commute with the
builders, and normal input annotations give normal equality/reflexivity.

This does not add equality reflection, eta, cumulativity, same-level
predicative symmetry or function extensionality. It does not assert that
arbitrary equality witnesses produce definitionally inverse transports,
or complete the dependent PHOAS interpreter.

## Environment and commands

Pinned environment: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1. Final inventory command, exit 0:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- bash -c 'rocq --version; dune --version; ocamlc -version; opam list --installed' > _build/indexed-equality.yyAdcb/versions-final.log 2>&1
version_status=$?
printf '%s\n' "$version_status" > _build/indexed-equality.yyAdcb/versions-final.exit
tail -8 _build/indexed-equality.yyAdcb/versions-final.log
exit "$version_status"
```

Fresh absolute Dune directory: `/tmp/pts-rk-indexed-equality.OmeFxC`.
Raw logs are retained locally in ignored `_build/indexed-equality.yyAdcb`.
For each `NN` below, the exact build command was the following with `NN`
replaced by the listed two-digit attempt number:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-indexed-equality.OmeFxC --display=short --no-buffer theories/self_interpreter/IndexedEquality.vo > _build/indexed-equality.yyAdcb/attempt-NN.log 2>&1
build_status=$?
printf '%s\n' "$build_status" > _build/indexed-equality.yyAdcb/attempt-NN.exit
tail -45 _build/indexed-equality.yyAdcb/attempt-NN.log
exit "$build_status"
```

| Attempt | Exit | First outcome |
| --- | --- | --- |
| 01 | 1 | `eq_specialize`: incomplete substitution equality. |
| 02 | 1 | Same goal; temporary `Show` recorded the double-shift substitution obligation. |
| 03 | 1 | `replace_as_rename` did not match the expanded substitution. |
| 04 | 1 | Additional simplification still did not expose that rewrite pattern. |
| 05 | 1 | Using the existing arrow-replacement lemma fixed specialization; normality needed a second nested renaming simplification. |
| 06 | 0 | Entire source compiled; eleven `Closed under the global context` reports. |

No timeout occurred. The ordinary logical-loadpath remapping warning remains;
it was not suppressed. The final successful compile was not a cached no-op.
The final source SHA-256 is
`7c45de73800705a9ea130719785fcecea020b72961de10556d55af9a3bab93df`.
`git diff --check -- theories/self_interpreter/IndexedEquality.v` exited 0.
No separate kernel/full-CI claim is made here; the coordinating agent runs
the final integrated audit.

## Closed assumption endpoints

`eq_type_sort`, `refl_case_typed`, `transport_typed`, `transport_refl`,
`refl_typed`, `refl_type_sort`, `refl_specializes`, `eq_type_replace`,
`refl_case_replace`, `eq_type_normal`, and `refl_case_normal` each printed
`Closed under the global context` in attempt 06.
