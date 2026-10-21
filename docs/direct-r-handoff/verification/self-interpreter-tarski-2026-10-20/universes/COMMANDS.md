# Original universe-code laws and all-rank identity witnesses

Source: theories/self_interpreter/TarskiUniverses.v.
SHA-256: bdbbe9578102a93d7b82b1a5c3833b38ca2922669edb1bf6bf1f0ea169f7df2e.
Working directory: /Users/akuklev/air/pts-rk.
Fresh build directory: /tmp/pts-rk-tarski-universes.768Wwo.
Raw local evidence: _build/tarski-universes.9hTKhb.

## Exact commands and results

`bash _build/tarski-universes.9hTKhb/RUN.sh 01` ran the following command,
with complete stdout/stderr retained in attempt-01.log and the immediately
captured numeric exit in attempt-01.exit:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-tarski-universes.768Wwo --display=short --no-buffer theories/self_interpreter/TarskiUniverses.vo
```

Attempt 01: exit 0, nine new public reports closed. This was the only build
attempt; no compiler failure, timeout or weakening of a theorem occurred.

Recursive kernel command (kernel.log/kernel.exit), exit 0:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-tarski-universes.768Wwo/default/theories PTSrk -Q /tmp/pts-rk-tarski-universes.768Wwo/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-tarski-universes.768Wwo/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.TarskiUniverses
```

The recursive loaded-context inventory contains only existing upstream
functional_extensionality_dep, with no type-in-type, unsafe fixpoints or
assumed positivity. All nine new public theorem reports are closed.

Installed versions were recorded by this command, exit 0
(versions.log/versions.exit):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune
```

Actual versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2 and Dune 3.23.1. Source hashing used
`shasum -a 256 theories/self_interpreter/TarskiUniverses.v`.
Scoped git diff --check exits 0; safety scan for admissions, axioms and
disabled checks has no matches (rg exit 1). Aggregate audit, pristine
comparison and full CI are separate parent-run checks.

## Proved object-language scope

`universe_law Ca E0 u` is the actual Leibniz equality type
IndexedEquality.eq_type 1 U0 (E0 u) Ca. From the original typings
Ca:U0, E0:C0->U0 and u:C0, `universe_law_sort` gives its exact sort U2.
Motive level one matches both arrow motives for the c=0 Tarski casts;
no same-level predicative equality symmetry is silently assumed.

`identity_universe_witness a` is the literal closed original PTS term
IndexedEquality.refl_case 1 U0 Ua. `identity_universe_typed` constructs its
original typing at universe_law Ua id0 Ua using the proved beta reduction
of id0 Ua to Ua and original conversion. `every_rank_has_universe_law`
bundles the concrete original closed code, decoder, law formation, law
inhabitant and inhabitant normality for EVERY external natural rank a.
It is not a finite-example test or an assumed all-rank witness.

Actual simultaneous replacement and renaming commute with law formation;
the closed identity witness is unchanged by replacement. A law annotation
is normal when its data are normal and its decoder is non-lambda neutral.
The identity witness itself is fully normal. Its specialized law annotation
contains the administrative redex id0 Ua and is not asserted normal;
`universe_law_identity_recovers` proves its reduction to the normal reflexive
equality type. `identity_universe_transport` proves actual beta recovery
through the reflexivity witness; direct typing of the two specialized cast
directions is a separate TarskiCasts endpoint.

No abstract universe-decoder law, internal type-reification algorithm,
global source-conversion coherence or complete dependent PHOAS quotation is
postulated or derived by this local module. Original PTS rules and all other
developments remain unchanged.
