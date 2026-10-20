# Specialized finite-palette PHOAS fidelity — 2026-10-20

`PHOASFaithful.v` covers `PHOASAlgebra.quoted`, whose polymorphic rank-pair
Abs/App variables are explicitly applied to two interpreted type arguments.
This differs from the earlier plain per-source-type handler representation.

The proof-device eraser removes those two arguments and reconstructs original
annotated STLC syntax. It is not an erased target language and is not the
object decoder. `erase_quoted`, `quoted_normal`, `quoted_injective` and
`quoted_conversion_injective` are proved for arbitrary neutral variable
palettes; source environments, types and palettes may differ. Only the shared
source-variable embedding must be injective. No disjointness of handler or
family variable indices is needed because the application-spine shapes
distinguish their roles. No target typing or infinite palette inhabitation is
assumed by these structural lemmas; original typing of an actual finite
closed package is a separate development.

The concrete regression reuses the independent executable STLC derivation
of `lambda x:o. (lambda y:o.y) x`. Both it and `lambda x:o.x`, after closing
their ground-type parameter, are original closed typed terms related by one
beta step. `beta_regression_neutral_codes` proves their specialized neutral
representations are not beta-convertible. Thus exact quotation fidelity is
not being mistaken for source-conversion preservation. This is a necessary
separation of quotation and semantic type interpretation, not a PHOAS no-go.

Exact compiler command (fresh initial Dune directory):

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
opam exec -- dune build --build-dir /tmp/pts-rk-phoas-faithful.ornnlp theories/self_interpreter/PHOASFaithful.vo
```

Literal launcher and complete outputs are retained in ignored
`_build/phoas-faithful.FCnLpz`: `RUN.sh`, `attempt-01.log` through
`attempt-07.log`, and `versions.log`. Attempts 01--04 exited 1 while rewriting
application-branch induction hypotheses across unfolded module aliases;
using the literal induction hypotheses as equality proofs fixed this.
Attempt 05 exited 1 on unsimplified Boolean factors in the normality proof;
explicit Boolean simplification fixed it. Attempt 06 exited 0 with the four
core endpoints. After adding the concrete regression, final attempt 07 exited
0 with six `Closed under the global context` reports. No timeout occurred.
Existing overlapping-loadpath warnings remain visible in the logs.

Toolchain inventory command (exit 0):

```sh
opam exec -- sh -c 'rocq -v; dune --version; ocamlc -version; opam list --installed --columns=name,version' > _build/phoas-faithful.FCnLpz/versions.log 2>&1
```

Observed pins: Rocq core 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2 and Dune 3.23.1. Root owns final aggregate fresh assumptions,
recursive kernel checking and full local CI; they are not claimed by this
module-only build. Scoped `git diff --check` exited 0.

Final source SHA-256:

```text
be380cd2859e255f4202f71316ca5ab5d9cf50ef6a8aaac4b47bac9467ffe073  theories/self_interpreter/PHOASFaithful.v
```
