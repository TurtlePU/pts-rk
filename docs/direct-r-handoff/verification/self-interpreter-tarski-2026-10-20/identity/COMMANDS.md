# Concrete identity Tarski product algebra

Date: 2026-10-20. Working directory: `/Users/akuklev/air/pts-rk`.
Source: `theories/self_interpreter/TarskiIdentity.v`.
SHA-256: `20687be9c166ad11d0bbd6774b85a1f91228780e579878419dcfa0257e6c2075`.
The coordinating agent owns Dune/Audit integration and the live handoff.

## Exact contract

Write `c=max(a+1,b)`. From original typings `A:U_a` and `B:A->U_b`,
the executable builder `identity_law a b A B` constructs the actual term

```
refl_case (c+1) U_c (Pi x:A. B x).
```

`identity_law_typed` proves that this term inhabits the concrete product
law relating the decoded dependent product and decoding the constructed
product code. The decoders are actual `BrownPalsberg.type_identity` terms;
the constructor is `TarskiProducts.identity_product`. Both sides reduce
to `Pi x:A.B x`, so original type conversion supplies the required law
type. `identity_product_law_sort` gives that type's original sort `U_(c+2)`.
The equality witness is constructed, not supplied as a theorem premise.

`identity_abs_typed` and `identity_app_typed` prove original typing of the
actual casted operations at `Pi x:A.B x` and `B u`, respectively. Their
proofs use direct application/conversion typing and the proved identity
law; they do not infer typing by subject expansion from the reductions.
`identity_abs_recovers` and `identity_app_recovers` prove beta reduction to
the literal `f` and `f u` without typing or normality premises.

The family `B` is genuinely dependent. No normal semantic payload is
computed or supplied; these builders contain only the given syntax and
actual lambda/product/application implementations of identity and transport.
No eta conversion, extensionality, cumulative universe inclusion, new
primitive, or assumed abstract product law is introduced. This is a local
identity algebra, not a complete dependent quoter, finite package, or
global conversion-coherence theorem.

## Toolchain and attempts

Fresh absolute Dune directory: `/tmp/pts-rk-tarski-identity.ZY8Twb`.
Ignored raw evidence: `_build/tarski-identity.vPKe1A`.
For each attempt number `NN` below, the build and immediate status capture
were exactly:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-tarski-identity.ZY8Twb --display=short --no-buffer theories/self_interpreter/TarskiIdentity.vo > _build/tarski-identity.vPKe1A/attempt-NN.log 2>&1
build_status=$?
printf '%s\n' "$build_status" > _build/tarski-identity.vPKe1A/attempt-NN.exit
tail -45 _build/tarski-identity.vPKe1A/attempt-NN.log
exit "$build_status"
```

| Attempt | Exit | First outcome |
| --- | --- | --- |
| 01 | 1 | Target not yet registered in Dune. |
| 02 | 1 | Target still not registered; an additional read-only `rg -n 'TarskiIdentity' theories/self_interpreter/dune` preceding the command found no registration. |
| 03 | 0 | First registered build compiled all six module assumption reports closed; dependency reports also closed. |

No proof compiler error or timeout occurred. The usual logical-loadpath
remapping warnings were not suppressed. Attempt 03 used fresh dependency
compilation, not a cached no-op.

Version command, exit 0 (`versions.log`, `versions.exit`):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune > _build/tarski-identity.vPKe1A/versions.log 2>&1
version_status=$?
printf '%s\n' "$version_status" > _build/tarski-identity.vPKe1A/versions.exit
```

Installed versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1.
`git diff --check -- theories/self_interpreter/TarskiIdentity.v` exits 0.
Source hashing uses `shasum -a 256 theories/self_interpreter/TarskiIdentity.v`.
The separate recursive kernel, aggregate assumption inventory, pristine
comparison and full CI are coordinating-agent checks, not inferred from
this targeted build.

## Assumption reports

The six endpoints `identity_law_typed`, `identity_product_law_sort`,
`identity_abs_typed`, `identity_app_typed`, `identity_abs_recovers`, and
`identity_app_recovers` each printed `Closed under the global context`.
