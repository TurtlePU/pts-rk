# Common infrastructure for the ordered-semiring interpretation

This directory supplies the thirteen common Rocq modules required by
[OrderedSemiring](../OrderedSemiring/README.md). Their stable logical library
name is `Interpretation_of_R`; the six required relational modules form its
[relational child library](relational/README.md). Neither a functional-R
interpretation nor a set-theoretic model is required.

All `.v` sources are copied byte-for-byte from
[akuklev/pts-rk at ffa7131](https://github.com/akuklev/pts-rk/tree/ffa7131be99bcbef3f1a787fce23126c3d310811/theories/Interpretation_of_R).
There were no uncommitted changes to those sources at import. The Dune module
list is restricted to the transitive dependency closure of the new proof;
the complete older arithmetic development is not part of this package.

The modules provide:

- `DirectRCommonCodes`, `DirectRKernel`: annotated term codes and the original
  `PTSrk.Typing.typ` interface, with no changes to the kernel or PTS rules.
- `DirectREval`, `DirectRCheck`: evaluation and a sound proof-producing
  checker; checker acceptance is used to derive original typing judgments.
- `DirectRStructural`, `DirectRLogic`, `DirectRPositive`: structural and
  logical proof constructors.
- `DirectRFiniteTables`, `DirectRFiniteObservations`, `DirectRFiniteUp`,
  `DirectRFiniteCertificates`: finite encodings and their typing lemmas.
- `DirectRIterations`, `DirectRSymbolic`: symbolic iteration and reduction.

Historical comments in copied sources, including old "unchecked" wording,
are preserved for provenance; they do not describe current verification.
The ordered-semiring README explains the public theorems, toolchain, and
fresh compilation and assumption checks.

From the repository root, using the documented Rocq/Equations switch:

```sh
dune build @theories/Interpretation_of_R/audit
dune build @theories/OrderedSemiring/audit
```
