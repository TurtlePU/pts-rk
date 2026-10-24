# Finite equational-model boundary — 2026-10-23

Compiler: `/Users/akuklev/.local/share/pts-rk-ci/opam/pts-rk-ci/bin/coqc`,
Rocq 9.2 compiled with OCaml 4.14.2. Only `Stdlib.Lists.List` and
`Stdlib.Arith.PeanoNat` are imported; no original PTS module changes.

From `/Users/akuklev/air/pts-rk`, for each attempt:

```sh
/Users/akuklev/.local/share/pts-rk-ci/opam/pts-rk-ci/bin/coqc -q \
  -o /tmp/pts-rk-finite-model-boundary.YnS1Vv/FiniteModelBoundary.vo \
  theories/CombinatoryLogic-rk/FiniteModelBoundary.v > LOG 2>&1
```

- `attempt-01.log`: exit 1. `f_equal` retained a beta redex in the resulting
  equality, so rewriting the K equation did not find its subterm. Also the
  nested module name initially masked the physical file name.
- `attempt-02.log`: exit 0. Added `cbn in Happly` and renamed the nested module
  `EquationalBoundary`; four closed `Print Assumptions` reports, no warnings.

Final source SHA256:
`a68e5e3d03088b4e68b8019c273a330dc7e3bd817142cdb1cd4cbf5eef799a86`.

The theorem requires a complete NoDup finite enumeration, total untyped
application, and the literal universal K equation. It does not establish
nonexistence of finite models of directed reduction, partial/typed/graded
application, or the actual MM0 signature. No Dune registration, full closure
check or documentation build is claimed by this isolated compilation.
