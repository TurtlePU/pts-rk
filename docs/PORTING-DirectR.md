# DirectR provenance

Original target: TurtlePU/pts-rk at
`723cf2ec61c737ae82ba33d2e7db44f650122b0e`.
Lab reference: clayrat/pts-dependent-types at
`7e6282d357c6f42217a9584f6c7493c594ae1aed`.
Reuse was explicitly authorized by the user as lab-owned code. No new license
is asserted for either repository and no existing notice is removed.

| Here | Reference | Changes |
| --- | --- | --- |
| DirectRCodes.NArrow | lab theories/PTS/Named.v | Adapted nonbinding-arrow assembly to numeric names and native scoped Term; kept explicit failure on unbound names. |
| DirectREval.v | lab theories/PTS/Eval.v, NormalOrder.v | Reimplemented pure head/full reduction on target annotated syntax; no primitive or annotation-erasure rule; retained target beta-step relation. |
| DirectRCheck.v | lab theories/PTS/Check.v, CheckSound.v | Adapted architecture for annotated-lambda synthesis; successful runs conclude target Typing.typ; uses target regularity/inversion/preservation instead of lab bidirectional relation. |
| Module split and proof organization | lab PCFTranslation/TranslateSound.v | Fixed certificates separated from indexed proofs and generators; no System-U theorem reused as a rank-system theorem. |
| DirectRSymbolic.v | preceding DirectR local development | Retained constructor-producing Ltac only for symbolic proof-family arguments; unchanged proof basis. |

No lab declarations of open contracts are imported as axioms. Common/Result.v
and Common/Traced.v are not copied: the adapter uses a small local result type.
No whole-file vendoring or extra external dependency is needed for this package.
All adapted proof scripts still require compilation in the target toolchain.
