# Native confluence and inversion incremental checks

All checks ran from `/Users/akuklev/air/pts-rk` with the exact command shape:

```sh
/tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries \
  -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
  -i theories/CombinatoryLogic-rk/agda \
  theories/CombinatoryLogic-rk/agda/MODULE.agda > LOG 2>&1
```

| Module | Log | Exit | Result |
| --- | --- | --- | --- |
| NativeInversion | inversion-01.log | 0 | Five UnsupportedIndexedMatch warnings in fixed-head inversions |
| NativeInversion | inversion-02.log | 0 | Generic computed Inversion family eliminates all warnings |
| NativeConfluence | confluence-01.log | 0 | One UnsupportedIndexedMatch warning in triangle |
| NativeConfluence | confluence-02.log | 0 | Generic lambda-shape elimination fixes warning; confluence complete |
| NativeConfluence | confluence-03.log | 0 | Normal uniqueness, universe/product injectivity; no warnings |
| NativeInversion | inversion-03.log | 0 | Original typing/rank uniqueness; no warnings |
| NativeInversion | inversion-04.log | 0 | Both final modules checked, including normal-result coherence; no warnings |

No failure, timeout, axiom, postulate, hole, unsafe option, or disabled check.
The first warning-producing definitions were replaced, not suppressed.
Dependency NativeAlgebra.agda is independently owned by the substitution task.
Root is responsible for the fresh complete import-closure check and durable
evidence archive; these incremental commands use ordinary local interfaces.

Final source hashes:

```text
12042f27ae6f6ede54198611df9a7b4ae136edca4724e24f384ebb69fa3eeb54  NativeConfluence.agda
0f0863590b4c5d4743afa14e1eaeb26e211a54a91f3d84ebd4b995261b1b4a37  NativeInversion.agda
```

`git diff --check -- theories/CombinatoryLogic-rk/agda/NativeConfluence.agda theories/CombinatoryLogic-rk/agda/NativeInversion.agda` exits 0.
