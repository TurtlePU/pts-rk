# Full original dependent source recursion

2026-10-21, working directory `/Users/akuklev/air/pts-rk`.
Source `theories/self_interpreter/RecursiveQuotation.v`, 156 lines,
SHA256 `38559f389ca8c7e7d343ddd4f0dfa95eefa5b030b2b2d06ef13b1c8855afd2f2`.

## Contract

`quote_derivation` is structurally recursive on the supplied independent
Type-valued FullSource derivation. It implements ALL SIX original rules.
Its other inputs are original computational context data, an actual finite
realized target state, a variable environment and the executable source
budget bound. Concrete empty initialization discharges the execution-state
invariants for every closed original derivation; these are not extra
premises of the final closed-source coverage theorem.

Sort/variable cases use existing actual programs. Products/lambdas thread
numeric checked-layer plans and push the literal source binder. Application
uses two independently computed code-alignment layers, then structurally
substitutes the retained codomain view. Conversion quotes its EXISTING
destination-formation child and allocates the actual equality repair from
independently recovered codes. `type_of_sort` handles the term/type-code
bridge without recursion on a synthesized validity derivation. No source
constructor, annotation, original conversion case or result type is erased.
No target-quotation oracle, semantic value lookup, axiom or unproved
coherence premise occurs.

The result carries original target typing, normal neutral programs, full
typed source-type views and strong literal-source beta recovery. The final
source-independent numeric decoder and closed/open coverage are assembled
separately in IndexedProgramInterpreter and FullDependentInterpreter.
This is not a polynomial/elementary overhead claim. No extracted runtime
or direct `vm_compute` performance benchmark is asserted; opaque proof
transports in indexed certificates can block kernel evaluation before
proof erasure even though the structural source recursion is checked.

## Commands and every attempt

Reuse of the phase's initially fresh absolute cache was coordinated to
avoid disk exhaustion. Each command was
`bash _build/recursive-quotation.WoXXwV/build.sh NN`, executing:

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-quotation-cache.ddlOA9 --display=short --no-buffer theories/self_interpreter/RecursiveQuotation.vo > "_build/recursive-quotation.WoXXwV/attempt-${attempt}.log" 2>&1
build_status=$?
printf '%s\n' "$build_status" > "_build/recursive-quotation.WoXXwV/attempt-${attempt}.exit"
```

| Attempt | Exit | First result |
| --- | --- | --- |
| 01 | 1 | Dependencies including final application compiled; own generic inherited-term helper needed explicit `Term nat` annotation. |
| 02 | 0 | All three helpers AND the full six-case recursive construction passed; four closed reports. |
| 03 | 0 | Stale under-construction header corrected; all four reports closed. |

No timeout or interrupted run. All raw logs/exits remain ignored in
`_build/recursive-quotation.WoXXwV/`. `check.sh` invokes pinned
`rocq check -silent -o` with the three standard stable mappings to the
copied theories, NormalizationComplexity and self_interpreter directories,
target `PTSrk.SelfInterpreter.RecursiveQuotation`. The recursive kernel check
exited0. Its inventory has only the unchanged upstream dependent functional-
extensionality entry, with no type-in-type, unsafe fixpoint, rewrite-rule or
assumed-positivity entry. Exact log/exit are retained independently.

All four own transitive Print Assumptions reports are CLOSED. Forbidden
source scan found no match; scoped `git diff --check` exited0. No Git/index
mutation. Versions remain Rocq9.2.0, Stdlib9.1.0, Equations1.3.2+9.2,
OCaml4.14.2 and Dune3.23.1 (recorded by the cache phase). Independent
read-only review passed every source case and the exact input boundary.
