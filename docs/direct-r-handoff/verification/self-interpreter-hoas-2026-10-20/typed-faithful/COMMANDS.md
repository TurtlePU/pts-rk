# Conditional normality and exact fidelity of indexed PHOAS prequotation

Working directory: `/Users/akuklev/air/pts-rk`.
Fresh build directory: `/tmp/pts-rk-typedhoas-faithful.oNYWSa/build`.
Every numbered attempt ran the following command with `NN` replaced by
its two-digit number, captured `$?` in `status`, displayed the log tail,
and exited with that same status:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-typedhoas-faithful.oNYWSa/build --display=short --no-buffer theories/self_interpreter/TypedHOASFaithful.vo > docs/direct-r-handoff/verification/self-interpreter-hoas-2026-10-20/typed-faithful/attempt-NN.log 2>&1
```

| Attempt | Exit | Result |
| --- | --- | --- |
| 01 | 1 | Type erasure needed `code_rename` for the codomain binder. |
| 02 | 0 | Exact type and term erasure compiled. |
| 03 | 1 | Sort case of renaming injectivity needed explicit equality substitution. |
| 04 | 0 | Full module; five closed transitive assumption reports. |

No timeout occurred. The five reports cover `erase_interpreted_type`,
`erase_prequote`, `prequote_normal`, `prequote_injective`, and
`prequote_conversion_injective`. Neutral family/Abs/App parameters are target
variables; no typing assumptions on an infinite neutral palette occur.
The type eraser removes family applications to recover exact original STLC
type syntax. The term eraser recovers `rename rho t`, including lambda
annotations. With injective `rho`, equal or beta-convertible prequotations
force literal source equality even across different derivations, source
environments, ground variables, result types, and neutral palettes.

These are conditional, generic prequotation results, not construction of a
closed originally typed neutral package. Finite palette construction remains
a separate obligation. No new axioms, source restrictions, or weakened
target judgments were introduced.

`source.sha256` records the final module. Toolchain versions are the same
freshly recorded pinned versions as `../hoas/versions.log` and
`../hoas/packages.log`. Aggregate fresh audit and recursive kernel checking
are performed by the parent task; this directory does not claim them.
