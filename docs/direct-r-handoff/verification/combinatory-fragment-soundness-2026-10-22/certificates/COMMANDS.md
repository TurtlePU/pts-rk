# Independent native/context/valuation certificate checkers

Working directory: /Users/akuklev/air/pts-rk. Only NativeCertificates.agda,
CertificateContexts.agda and NativeCanonicity.agda were added. Existing sources, staged state,
and other agents' changes were preserved; no commit/staging operation.

Every compilation used this command with the indicated module and log:

```sh
/tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries \
  -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
  -i theories/CombinatoryLogic-rk/agda \
  theories/CombinatoryLogic-rk/agda/MODULE.agda > LOG 2>&1
```

Agda version: 2.8.0-3d04bac. Ordinary incremental interfaces used; the root
will run the complete fresh safe closure separately.

| Module | Log | Exit | Result |
| --- | --- | --- | --- |
| NativeCertificates | attempt-01.log | 0 | Independent grammar and soundness |
| NativeCertificates | attempt-02.log | 0 | Every original Typ/Beta/Step certified |
| NativeCertificates | attempt-03.log | 0 | Decidable, proposition-valued acceptance |
| CertificateContexts | context-01.log | 0 | Context/valuation checking and adequacy |
| CertificateContexts | context-02.log | 0 | Proposition lemmas and executable regressions |
| NativeCanonicity | canonicity-01.log | 42 | Implicit-argument parse error |
| NativeCanonicity | canonicity-02.log | 0 | External Void canonicity, no warnings |

All successful compiler runs completed without warnings. No timeouts. The
canonicity parse error was fixed by supplying explicit implicit-term types.
The initial broad safety search also matched question marks
in legitimate decision-procedure identifiers; the refined safety scan below
has no matches (rg exit 1). Whitespace check exits 0.

```sh
git diff --check -- theories/CombinatoryLogic-rk/agda/NativeCertificates.agda theories/CombinatoryLogic-rk/agda/CertificateContexts.agda
rg -n 'postulate|TERMINATING|NON_TERMINATING|NO_POSITIVITY|allow-unsolved|\{!!\}' theories/CombinatoryLogic-rk/agda/NativeCertificates.agda theories/CombinatoryLogic-rk/agda/CertificateContexts.agda
shasum -a 256 theories/CombinatoryLogic-rk/agda/NativeCertificates.agda theories/CombinatoryLogic-rk/agda/CertificateContexts.agda
```

Frozen source hashes:

```
cda5ee4ceef0a4b79c97201d56782790115ebb561261a1421c9f4f4c8d01eb6f  NativeCertificates.agda
428481c0aa6c3c8e43e933a2800a1f189a98aaabb314c1612990148b4318658a  CertificateContexts.agda
a5195ea0caedf37104fb79b8269cfd0e8cb7c2e4554ed2677987198e4fe2e9dc  NativeCanonicity.agda
```

The independent acceptance predicate contains only local syntax equations
and recursive checks. No native Typ/WellFormed/TypedSub judgment occurs in
certificate fields or acceptance predicates; each is a soundness conclusion.
These proofs support a graded syntactic interpretation. They do not provide
fixed finite first-order model closure or internal consistency by themselves.

NativeCanonicity proves normal-Void-empty, Void-empty, accepted-Void-rejected,
and fragment-Void-empty for Void = Pi X:U_0.X. The global statement uses the
computed original rank-bound normalizer, without a rank/termination input.
It is an EXTERNAL Agda metatheorem; it supplies neither an internal PTS
consistency inhabitant nor finite first-order model existence.
