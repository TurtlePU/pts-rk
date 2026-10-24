# Indexed Horn encoding — 2026-10-23

New source only: theories/CombinatoryLogic-rk/IndexedHornEncoding.v.
No previous proof, Dune registration, Agda source or shared note was edited.
Pinned toolchain reports Rocq 9.2, compiled with OCaml 4.14.2.

The three isolated compile attempts copy the new source into this directory
and execute the same command below, with output retained in attempt-01.log,
attempt-02.log and attempt-03.log. They return 1, 1 and 0 respectively.
Attempts 01 and 02 fail only while rewriting substitution of shifted query
syntax in specialize_typed. Attempt 03 explicitly simplifies fin_match after
replace_rename and succeeds with 17 closed public assumption reports.
Their wall durations reported by the command tool are 0.21274325 seconds,
0.194857333 seconds and 0.642240125 seconds. UTC start/end times were not
separately captured for these short compilation attempts.

```sh
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
cp theories/CombinatoryLogic-rk/IndexedHornEncoding.v /tmp/pts-rk-indexed-horn.MHrkIn/IndexedHornEncoding.v
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- rocq compile \
  -Q /tmp/pts-rk-internal-horn.6x5cr6/default/theories PTSrk \
  -Q /tmp/pts-rk-internal-horn.6x5cr6/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-internal-horn.6x5cr6/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-internal-horn.6x5cr6/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -Q /tmp/pts-rk-indexed-horn.MHrkIn PTSrk.Combinatory \
  /tmp/pts-rk-indexed-horn.MHrkIn/IndexedHornEncoding.v
```

The complete recursive kernel check executes the same five -Q mappings,
replacing `compile .../IndexedHornEncoding.v` with
`check -silent -o ... PTSrk.Combinatory.IndexedHornEncoding`.
It passes, exit 0, 20:33:21–20:33:33 UTC; kernel.start, kernel.end,
kernel.exit and kernel.log record the exact result. The full context inventory
is byte-for-byte equal (diff exit 0) to the previous fresh pristine inventory:

```sh
diff -u \
  <(sed -n '/CONTEXT SUMMARY/,$p' _build/combinatory-internal-horn-audit.JMyhh0/upstream-kernel.log) \
  <(sed -n '/CONTEXT SUMMARY/,$p' /tmp/pts-rk-indexed-horn.MHrkIn/kernel.log)
```

Only inherited functional_extensionality_dep occurs in the complete recursive
inventory; no type-in-type, unsafe fixpoints or assumed positivity.
All 17 new public reports themselves are closed. This isolated test reuses
the previous fresh dependency objects; it is not a fresh full-library build.

Frozen source SHA256:
792c3865e35d701996e87dc543dc308be5da6aab925c8f9cef6ada06ce1d2bcc.

The proof encoding depends only on the fixed finite clause list and a native
query of the Church code type. No model, truth table, source typing, decoder
or canonicity premise occurs. Query types have rank 1, predicate types rank 2,
and proof types rank 3, using exactly the original rank rule. These are type
formation ranks, not syntax-size or global normalization-rank bounds.
