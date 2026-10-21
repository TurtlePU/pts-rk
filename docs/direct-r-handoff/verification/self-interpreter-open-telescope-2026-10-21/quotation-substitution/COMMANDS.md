# Structural substitution of originally typed quotation views

2026-10-21; working directory `/Users/akuklev/air/pts-rk`.
Source `theories/self_interpreter/QuotationViewSubstitution.v`, 292 lines,
SHA256 `e0ad20a1800b7b9fd97264f8ef72c1f13cea73c414e13ffb66a24b683872cfa3`.
Only new owned source/evidence edited; no Git/index mutation or frozen edit.

## Contract

`substitute_view` is structurally recursive on finite supplied code-view data.
It preserves the LITERAL target substitution of every root code, original
typing, normality/neutrality, strong source recovery and recursively retained
product children. Variable replacement takes only the argument's source shape;
its independently substituted root certificate and original sort uniqueness
construct the new product view. The binder case derives the lifted realization
into the literal substituted source context. No generated source derivation
is passed recursively to a quoter, and no Prop existential is extracted.

`substitute_shape` supplies the parallel term-shape transformation.
`instantiate_codomain` specializes to an ACTUAL originally typed normal neutral
represented argument q recovering u. It returns the complete view of B[u]
with root cache exactly Bc[q]. This is the executable dependent-application
bridge; it does not itself claim a six-case all-source quoter.

## Commands and all attempts

Reuse of this phase's initially fresh `/tmp/pts-rk-quotation-cache.ddlOA9`
was coordinated because disk space was low. New ignored raw directory:
`_build/quotation-view-substitution.ps1WOt/`. Each numbered attempt ran
`bash _build/quotation-view-substitution.ps1WOt/build.sh NN`, executing:

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-quotation-cache.ddlOA9 --display=short --no-buffer theories/self_interpreter/QuotationViewSubstitution.vo > "_build/quotation-view-substitution.ps1WOt/attempt-${attempt}.log" 2>&1
build_status=$?
printf '%s\n' "$build_status" > "_build/quotation-view-substitution.ps1WOt/attempt-${attempt}.exit"
```

| Attempt | Exit | First result |
| --- | --- | --- |
| 01 | 1 | Concurrent QVR dependency, Pi certificate inference at line100. |
| 02 | 1 | Own recursive call needed explicit dependent parameters. |
| 03 | 0 | Full structural code-view substitution, five closed. |
| 04 | 1 | Single-substitution variable constructor needed nat/scope arguments. |
| 05 | 1 | Single-typing change tactic needed explicit shifted annotation. |
| 06 | 0 | Shape wrapper and actual codomain instantiation, seven closed. |

No timeout. Existing loadpath warnings retained. Recursive check uses retained
`check.sh` with the same three -Q mappings as the cache evidence and final
module `PTSrk.SelfInterpreter.QuotationViewSubstitution`; its raw kernel log
and exit are retained separately. Recursive kernel check exited0, with only
the unchanged upstream dependent functional-extensionality entry in its
loaded inventory and no unsafe checks. All seven own transitive reports are CLOSED. Toolchain versions
are recorded by the cache phase's versions.sh (exit0); no environment change.
Scoped git diff --check exited0. Coordinator owns aggregate/pristine audit.

## Authorized mechanical alias cleanup

To prevent exported alias environments growing exponentially in the final
assembly, the coordinator authorized removal of the six local abbreviation
declarations and mechanical expansion of their references. No definition,
theorem statement or proof obligation changed. Current source is286 lines,
SHA256 `85fed308521a58cbd90365185d6575689457c6d77c9ded3614da5265b604af30`.
FullQuotation attempt05 rebuilt the cleaned source with seven CLOSED
reports; its artifact is56KB. The subsequent FullQuotation recursive kernel
check exited0 including this dependency. See sibling full-quotation evidence
for the exact retained commands/logs; historical evidence above is unchanged.
