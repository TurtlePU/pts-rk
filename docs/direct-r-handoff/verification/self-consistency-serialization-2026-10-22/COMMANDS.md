# Homogeneous certificate serialization — 22 October 2026

HEAD remains `6a8dc984fb59a9b3743503cd405ffe59a31d1978`. No stage, commit or
push in this continuation. Existing unrelated work is preserved.

## Contracts and boundary

Three modules extend PTSrk.SelfConsistency, using only the original PTSrk
kernel, Stdlib and Equations:

- `StructuralCodes`: one external tree datatype with a finite tag alphabet
  and binary pairing. Natural labels/indices have canonical binary encodings,
  with no unbounded natural-valued atom. Original scoped terms retain lambda
  annotations. Positive/natural/term codecs satisfy both inverse laws;
  finite indices are checked against the requested scope.
- `CertificateSerialization`: exact codecs for all seven beta locations,
  four equality constructors, six typing rules, context certificates and
  complete inputs (including the encoded scope). Both inverse laws hold for
  every class. Syntax injectivity includes complete inputs across scopes.
  Successful parsing re-encodes the literal supplied tree: no field is
  discarded, normalized or repaired. The raw checker is sound and covers
  every original derivable judgment in a well-formed context.
  `raw_compress` preserves acceptance; its exact domain is successful
  structural decoding, independently of acceptance. Malformed trees remain
  code values, rejected by the checker; eventual resource admission must
  also cover those trees.
- `SerializationBounds`: exact positive-bit encoding size, support-size
  bounds including annotations/context proofs/conversion instructions, and
  `decoded_label_bound`: every compressed label of a decoded complete input
  is bounded by that raw tree's node count. Repeated fields are charged in
  full. This is a representation-size result, not a machine operation-cost,
  proof-transport or bounded-history theorem.

Regression examples cover accepted identity, rejected malformed context,
compression of that rejected input, out-of-scope variables, wrong tuple
arity, missing lambda annotation, and noncanonical binary zero.
The constructor tags are structural certificate syntax; no raw HOAS envelope
is added to the self-interpreter. No Church numeral conversion or CPS work.

Fixed homogeneous data here are Rocq data, not yet an internal PTS carrier.
Next construct actual original PTS carrier/guard terms at explicit fixed
ranks and prove finite-table laws for arbitrary guarded inputs. Internal
decoding, resource admission and all-budget soundness remain open.

## Fresh verification

```
bash docs/direct-r-handoff/verification/self-consistency-serialization-2026-10-22/AUDIT.sh
```

Every stage exits 0, 16:34:14–16:34:45 UTC:

- Logs: `_build/self-consistency-serialization-audit.IjtwrQ`.
- Fresh absolute Dune build: `/tmp/pts-rk-serialization-fresh.ZI6rB9`.
- Pristine original: `/tmp/pts-rk-serialization-pristine.RnLWyC`, from
  `723cf2ec61c737ae82ba33d2e7db44f650122b0e`.
- Pristine build 16:34:15–18, recursive pristine kernel check 16:34:18–24.
- New dependency closure 16:34:24–29; separate public audit 16:34:29–33:
  **85 endpoints, 85 closed reports** (43 previous plus 42 new).
- Recursive kernel check 16:34:33–45; the complete context inventory exactly
  matches pristine. Only unchanged upstream
  `Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`
  occurs. No type-in-type, unsafe fixpoint or assumed positivity.
- Original-source comparison, safety scan and before/after source-manifest
  equality all pass. The four previous certificate/compression modules retain
  their recorded source hashes exactly.

Versions: Rocq 9.2, Stdlib 9.1, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1. Full versions, commands, timestamps, outputs and exit codes are
in the fresh log directory. The audit's explicit failure propagation and
separate public-output counting are retained. Full repository CI was not rerun.

Incremental command setup is the same pinned environment as AUDIT.sh.
All attempts are retained in `_build/self-consistency-serialization-progress`:

```
opam exec -- dune build -j 2 theories/self_consistency/StructuralCodes.vo
# attempts 01–02
opam exec -- dune build -j 2 theories/self_consistency/CertificateSerialization.vo
# attempts 03–12
opam exec -- dune build -j 2 theories/self_consistency/SerializationBounds.vo
# attempts 13–17
```

Failures (exit 1): 01, 03, 04, 06, 07, 08, 11, 13, 14, 15.
Successes (exit 0): 02, 05, 09, 10, 12, 16, 17.
Failures concern definitional reduction of binary encodings, existing `&`
notation versus sigma syntax, a generated doubled slash, scope of a structural
proof recursion, parser tactic focus, an omitted import, and list-length
simplification. All are fixed. Repeated parser-field proofs were then factored
into common tactics; attempt 17 recompiles that final version successfully.
No proof or parser contract was weakened.

## Exposition

```
bash theories/self_consistency/build-note.sh DIRECT_ROADMAP
swift docs/direct-r-handoff/verification/self-consistency-direct-roadmap-2026-10-22/inspect.swift theories/self_consistency/DIRECT_ROADMAP.pdf _build/self-consistency-serialization-progress/pdf
```

Build and validation exit 0 on the first attempt, in
`/tmp/pts-rk-consistency-note.M0yWcS`. PDF inspection exits 0: nine nonempty
pages, four links, primary citation, required text, no unrendered mathematics,
all pages rendered. Changed pages 2 and 5 were visually reviewed. No LaTeX,
overflow, underflow or missing-character diagnostics. Raw note and inspection
logs/renderings are retained in the progress directory. Shell syntax and
scoped whitespace checks also pass.

```
4b3e63d9a75d599d0f2a91ee495a8c4c1989193059b9dac4c56bd5f8a1ab399c  StructuralCodes.v
2a0b52bd67b8272402c042851a56354a70153a2b42588f781135dc8ba38e205b  CertificateSerialization.v
9e1cec00ca5df1a521aafeafb9b1cd8bf52a5ac155ceeca850ee37e77747b72f  SerializationBounds.v
9eb3435188bcb2313abd3daaf330637c4516fa5c2a454104a288c2f109fa0f84  Audit.v
65eb771174397991e20e7523ba7bbc93095318d26b34f38586df051cd541c6e1  dune
a4c9827663ad3ebe41a8da70d4228c36cea914ef6f81f3eef8125d8fa650b828  DIRECT_ROADMAP.tex
18e5d1ff77342df6ecf73b21e702cff7077a04f226b55b82c71e65d2cad7e3eb  DIRECT_ROADMAP.pdf
```
