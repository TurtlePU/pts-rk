# Church AST faithfulness — 20 October 2026

This module proves exact syntax injectivity for the full original annotated
Term nat n grammar at each fixed source scope n. It assumes neither source
typing nor source normality. Labels, variable indices, product domains,
lambda annotations and binder bodies are all preserved. The scope n itself
is not encoded; identical trees can inhabit different ambient scopes.

quote_conversion_iff additionally proves that original beta conversion of
two closed representations is equivalent to equality of BOTH external
carrier ranks and original source terms. It combines syntactic injectivity
with ChurchSyntax.quote_normal and the original common-reduct theorem.
It is not an object-language decoder or a typed dependent self-interpreter.

Initial fresh Dune directory: /tmp/pts-rk-church-faithful.yQgtyP.
The environment is explicitly set in BUILD.sh and CHECK.sh. Package versions
are recorded in versions.log. No package installation or source-rule change.

Exact build invocations from the repository root:

```sh
bash docs/direct-r-handoff/verification/self-interpreter-church-2026-10-20/faithful/BUILD.sh 01
bash docs/direct-r-handoff/verification/self-interpreter-church-2026-10-20/faithful/BUILD.sh 02
bash docs/direct-r-handoff/verification/self-interpreter-church-2026-10-20/faithful/BUILD.sh 03
bash docs/direct-r-handoff/verification/self-interpreter-church-2026-10-20/faithful/CHECK.sh
```

Attempt 01 proves body and quotation injectivity. Attempt 02 adds external
rank injectivity and normal-conversion helpers. Attempt 03 adds conversion
injectivity and its iff formulation, printing five closed assumption reports.
All three compilations exit 0. No compiler error, timeout or interruption
occurred. The known logical-loadpath remapping warning remains in raw logs.

CHECK.sh recursively kernel-checks the compiled ChurchSyntaxFaithful module;
the numeric result is in status.tsv and the full inventory is in kernel.log.
It exits 0; the loaded context reports only the unchanged upstream
functional_extensionality_dep and no type-in-type, unsafe fixpoints or
assumed positivity. The five new theorem-level reports are closed.
ChurchSyntax typing development continued independently afterward, so the
parent's final combined fresh audit is authoritative for the complete library.
No full CI result is implied by this local module audit.
