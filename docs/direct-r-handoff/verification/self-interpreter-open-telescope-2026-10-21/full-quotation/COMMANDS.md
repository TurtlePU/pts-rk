# Numeric quotation plans and typed constructor assembly

2026-10-21. Working directory `/Users/akuklev/air/pts-rk`.
`theories/self_interpreter/FullQuotation.v`: 366 lines,
SHA256 `dc2d62c93f80c69d28b5033e6379120c3ecf346adcf4d744b40a2b645b2c5f52`.

## Checked boundary

Plans contain only numeric checked-layer budgets. `advance` preserves the
literal source context while deriving original target well-formedness and
the actual identity substitution. `reframe_judgment` retains literal root
programs and codes, comparing contexts and inherited maps rather than
proof-bearing state records. Composition and binder push commute with
global growth through explicitly proved equations. Product/lambda result
constructors close actual child programs, retaining annotations. The rank
bound uses independently supplied original source evidence.

This module deliberately does not yet assert all-source coverage; the
structural source recursion lives in the separate RecursiveQuotation module.

## Exact commands and attempts

The initially fresh phase cache `/tmp/pts-rk-quotation-cache.ddlOA9` was reused
by coordination to preserve disk space. Raw logs are retained, ignored, in
`_build/full-quotation.1xNEwK/`. Each numbered run executed
`bash _build/full-quotation.1xNEwK/build.sh NN`:

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-quotation-cache.ddlOA9 --display=short --no-buffer theories/self_interpreter/FullQuotation.vo > "_build/full-quotation.1xNEwK/attempt-${attempt}.log" 2>&1
build_status=$?
printf '%s\n' "$build_status" > "_build/full-quotation.1xNEwK/attempt-${attempt}.exit"
```

| Attempt | Exit | First result |
| --- | --- | --- |
| 01 | 130 | Explicit SIGINT after exported module-alias cloning exceeded14GB RSS. |
| 02 | 130 | Explicit SIGINT; alias-free source prepared after profiling. |
| 03 | 0 | Original plan/state transport, seven closed reports. |
| 04 | 1 | Advance projections hidden from inherited-map rewrite. |
| 05 | 1 | Same projection issue in push case; cleaned QJ/QVS dependencies rebuilt. |
| 06 | 1 | Rank equality rewrite did not match the elaborated projection. |
| 07 | 1 | Arithmetic automation could not use that projection equality. |
| 08 | 1 | Diagnostic displayed exact rank equality/goal; automation still failed. |
| 09 | 1 | Explicit equality elimination fixed rank bound; request map needed its equation. |
| 10 | 0 | Complete infrastructure, sixteen closed reports. |

No timed-out run. The retained direct `profile.sh` executed `rocq c -time`
inside the copied cache source tree, with the same three logical mappings;
it was interrupted (exit1) after identifying Require41s, QC alias9s and QJ
alias36s. A minimal `Local Module` probe was rejected (exit1) because Rocq9.2
does not support the local attribute on Module. All owned FullQuotation
module aliases were replaced by fully qualified references; its initial
compiled artifact was21KB. The coordinator additionally authorized strictly
mechanical alias removal in owned QJ/QVS, rebuilt in attempt05; see their
evidence addenda. No original theorem, rule or proof obligation was changed.

`bash _build/full-quotation.1xNEwK/check.sh` ran pinned `rocq check -silent -o`
with mappings of the copied theories, NormalizationComplexity and
self_interpreter directories to their stable libraries, checking
`PTSrk.SelfInterpreter.FullQuotation` recursively. Exit0; only unchanged
upstream dependent functional-extensionality inventory, no unsafe entries.
This rechecked the alias-cleaned QJ/QVS dependencies too. All sixteen own
transitive reports are CLOSED. Source scan found no forbidden declaration;
scoped `git diff --check` exited0. No Git/index mutation. Versions unchanged
from the cache evidence: Rocq9.2.0, Stdlib9.1.0, Equations1.3.2+9.2,
OCaml4.14.2, Dune3.23.1. Independent infrastructure review passed.
