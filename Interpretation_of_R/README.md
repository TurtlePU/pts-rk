# Direct interpretations of arithmetic R

The parent directory is shared infrastructure; `relational/` and `functional/`
are separate Rocq libraries. Neither interpretation imports the other.
The original `PTSrk` kernel remains unchanged in `theories/`.

| Directory | Rocq library | Contents |
| --- | --- | --- |
| This directory | `Interpretation_of_R` | Annotated term builders, native checker, structural and negative logic, telescopes, finite tables and selector certificates, shared source countermodel |
| `relational/` | `Interpretation_of_R.relational` | Unary carrier, relational syntax/translation/deduction, all axiom schemes, ground correctness, nonfaithfulness, completed Theorem 4 |
| `functional/` | `Interpretation_of_R.functional` | Four-constructor carrier, certified observations, completed Theorem 7 and effective original-PTS witnesses |

## Independent build and assumption audits

From the repository root, in the configured Rocq/Equations switch:

```sh
dune build @Interpretation_of_R/relational/audit
dune build @Interpretation_of_R/functional/audit
```

Each target depends only on its own interpretation, the shared library and the
original kernel. Use a fresh `--build-dir` to execute `Print Assumptions` again;
an incremental successful command may reuse previous audit output.
`bash tools/check-local-ci.sh` also checks pristine upstream and all existing
development stages. The external set-model development remains separate in
`ZFC_model/` and is not a dependency of either interpretation.

The old `From PTSrk Require Import DirectR...` imports have been replaced by
the corresponding library imports. Module basenames and theorem names remain
unchanged, except extracted common definitions now live in `CommonCodes`,
`Iterations`, `FiniteCertificates`, and `Structural.arrow_beta`.
Functional `Codes` includes the shared builders; it does not redefine the PTS.
See the live handoff STATE for exact build evidence and remaining obligations.
