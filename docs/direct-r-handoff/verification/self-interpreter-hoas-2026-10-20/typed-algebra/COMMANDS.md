# Actual indexed PHOAS identity-algebra typing

Working directory: `/Users/akuklev/air/pts-rk`.
Build directory: `/tmp/pts-rk-typedhoas-faithful.oNYWSa/build`, freshly created
for the sibling faithfulness module before this new module was introduced.
Every attempt ran the following exact command with `NN` replaced by its
two-digit number, captured `$?` in `status`, displayed the log tail,
and exited with that same status:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-typedhoas-faithful.oNYWSa/build --display=short --no-buffer theories/self_interpreter/TypedHOASAlgebra.vo > docs/direct-r-handoff/verification/self-interpreter-hoas-2026-10-20/typed-algebra/attempt-NN.log 2>&1
```

| Attempt | Exit | Result |
| --- | --- | --- |
| 01 | 1 | Concurrent TypedHOAS substitution proof was incomplete at line 271. |
| 02 | 1 | Two-argument specialization left unreduced lifted substitutions. |
| 03 | 1 | Diagnostic goal output for the same lifted substitutions. |
| 04 | 1 | Concurrent TypedHOAS bounded-typing arithmetic proof was incomplete at line 332. |
| 05 | 1 | Same dependency failure; no local proof result obtained. |
| 06 | 1 | Over-strict rewrite in specialization cleanup found no direct matching subterm. |
| 07 | 1 | Cleanup needed ordinary simplification of dependent finite-index casts. |
| 08 | 0 | Full module, five closed transitive assumption reports. |

No timeout occurred. The five reports cover `specialize_abs`, `specialize_app`,
`actual_identity_cases_typed`, `identity_interpretation_typed`, and
`typed_identity_interpretation`. The two specialization lemmas apply the
original typing application rule twice; no subject-expansion assumption is
used. Original conversion relates identity-specialized interpretation types
to the original source types via proved common reducts.

The final endpoint takes independent source derivation data, original typing
of the ground-type variable and the existing original source environment
typing. It proves that the actual computed `identity_interpretation d` has
the original source type and strongly beta-reduces to the literal original
source. It does not assert normality of this identity-specialized syntax or
construct a closed neutral PHOAS package. Actual replacement naturality and
replacement-based recovery are separate checked theorems in `TypedHOAS.v`.

`source.sha256` records the frozen module. Exact pinned versions are shared
with `../hoas/versions.log` and `../hoas/packages.log`. The parent task owns
the aggregate fresh audit and recursive kernel check; these local logs do
not claim those broader checks.
