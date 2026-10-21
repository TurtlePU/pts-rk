# Whole dependent-spine equality

Date: 2026-10-21. Repository: `/Users/akuklev/air/pts-rk`.
Source: `theories/self_interpreter/TelescopeEquality.v`, 494 lines.
Frozen SHA-256:
`f9791c487fd656cc4a43ce7531204d0f38b3c444bf5a3913b7cdac77482de47f`.
Only this new module and scoped evidence were edited; the coordinator owns
Dune, Audit and shared prose. No Git mutation.

## Checked contract and boundary

The actual object-language `eq_type` quantifies a predicate over an independently
formed dependent telescope and applies it to two independently typed whole
argument spines sharing the same base substitution. Its original formation
rank is `max (S (CT.ceiling rs)) (S d)`. The actual `refl_case` is typed;
`transport_function_typed` and `transport_typed` type the real predicate
application and value transport. Reflexive transport reduces to the literal
input. Exact target-substitution equations and guarded full normality are
proved; normality requires the actual substituted predicate type and spine
arguments to be normal, not merely the uninstantiated telescope.

`map_case_typed` implements joint dependent congruence using an independently
typed base-preserving substitution from a second telescope into the first.
It maps whole-spine equality to equality of the composed spines at the SAME
predicate level. The predicate transformer is an actual lambda closure, with
original typing and actual application recovery derived in the module;
neither is supplied as a desired-result premise. `map_case_refl` reduces the
program at reflexivity to literal reflexivity on the composed spine, without
eta. `map_case_normal` states explicit normal-annotation, normal-map and
normal-neutral-evidence guards. `rank_bounded` gives the numerical bound
`k+2` for bounded rank vectors/predicate ranks; it is not cumulativity.

This covers joint dependent substitution congruence over one fixed ambient
base. It does not prove arbitrary pointwise-to-function equality, transport
an unproved equivalence between changing bases, supply whole-source
coherence, or construct a recursive dependent PHOAS quotation.

## Exact build and failures

Fresh directories were created with `mktemp -d`:
`/tmp/pts-rk-telescope-equality.mri53d` (absolute Dune directory) and
`_build/telescope-equality.szZrul` (ignored raw logs/scripts).
Each attempt ran `bash _build/telescope-equality.szZrul/RUN.sh NN`:

```sh
cd /Users/akuklev/air/pts-rk
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
timeout 1200 opam exec -- dune build \
  --build-dir=/tmp/pts-rk-telescope-equality.mri53d \
  --display=short --no-buffer -j 2 \
  theories/self_interpreter/TelescopeEquality.vo
```

The retained driver writes all output to `attempt-NN.log` and records the
exact process exit in `status.tsv`; it does not hide a failing compiler exit.

| Attempt | Exit | First outcome |
| --- | --- | --- |
| 01 | 1 | Target not registered yet; no proof checking. |
| 02 | 1 | Shifted typing needed an explicit unfolding of `shift`. |
| 03 | 1 | Incorrect substitution lemma name; changed to existing `replace_replace`. |
| 04 | 1 | Pointwise spine substitution equality needed the explicit structural `run_ext` lemma. |
| 05 | 1 | Normality rewrite also needed explicit `shift` unfolding. |
| 06 | 0 | Complete equality, transport, naturality and normality core; nine closed reports. |
| 07 | 1 | Unused motive parameter needed explicit `d : nat`. |
| 08 | 1 | Closure-renaming rewrite needed explicit `shift` unfolding. |
| 09 | 1 | Inherited-variable typing needed the literal context-lookup form. |
| 10 | 1 | Reverse base-lookup rewrite needed the explicit telescope argument. |
| 11 | 1 | Tactic placeholder could not infer the target term; made explicit. |
| 12 | 1 | Setoid rewrite under `run` lacked a Proper instance; used explicit proved spine extensionality instead. |
| 13 | 1 | Rewrite occurrence 2 did not exist; only one equality type was present. |
| 14 | 0 | Actual dependent-map typing and application recovery compiled. |
| 15 | 0 | Literal map reflexivity, guarded normality and rank bound; all fifteen final reports closed. |

No timeout, disk failure, admitted proof, new axiom, disabled check, theorem
weakening, or frozen-library edit occurred. Earlier successful attempts are
intermediate, not substitutes for the final attempt15 result.

## Recursive kernel and toolchain

`bash _build/telescope-equality.szZrul/CHECK.sh` exited0. Its exact check was:

```sh
timeout 1200 opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-telescope-equality.mri53d/default/theories PTSrk \
  -Q /tmp/pts-rk-telescope-equality.mri53d/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-telescope-equality.mri53d/default/theories/self_interpreter PTSrk.SelfInterpreter \
  PTSrk.SelfInterpreter.TelescopeEquality
```

`kernel.exit` is 0. The recursive loaded-library inventory contains only the
pre-existing upstream dependent-functional-extensionality entry; there is
no type-in-type, unsafe (co)fixpoint or assumed positivity. This inventory is
distinct from all fifteen CLOSED own theorem reports. Final aggregate
pristine comparison belongs to the coordinator's later frozen audit.
The explicit forbidden-declaration scan returned1 (no matches), recorded in
`safety.exit`; source hashing is retained in `source.sha256`.

`VERSIONS.sh` ran `date -u`, `git rev-parse HEAD`, `rocq -v`, `dune --version`,
`ocamlc -version`, `opam --version`, and full `opam list --installed
--columns=name,version`, retained in `versions.log`. Versions: Rocq9.2.0,
Stdlib9.1.0, Equations1.3.2+9.2, OCaml4.14.2, Dune3.23.1, opam2.6.1.
HEAD at the check was `e822cd62df393faf4d5e4ed0c4c8fed173ccba6f`.
Raw scripts/logs are local generated evidence, not committed artifacts.

Independent read-only review by the source-validity/telescope-recovery owner
passed against the frozen hash: fixed-base dependent maps and both spines
are independently typed; no pointwise function extensionality or unproved
changing-context transport is hidden. No correction was requested.
