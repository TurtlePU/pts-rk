# Global contextual equality-only field allocation

Date: 2026-10-21. Source: `theories/self_interpreter/ContextualEqualityExtension.v`.
Frozen SHA-256: `b06add120ff0abe48fe7f5b1ba1cbcc2cafc8fb2e4704bd3cf0173366494a6a7`.
Only this module and scoped evidence were edited; coordinator owns shared
Dune/Audit/prose. No Git mutation.

## Contract

An independently formed local dependent telescope is abstracted into a new
GLOBAL field declaration over the preceding base context. Its declaration
is the literal telescope closure of original Leibniz equality. Given an
actual closed base TypedSub, independent original endpoint typings, and
conversion of the two actually filled endpoints, the module constructs a
closed NORMAL field realizer and derives the extended original TypedSub.
No local proof variable, target quotation premise or semantic-value lookup
is assumed. Normal declaration formation separately requires normal domain
annotations and normal carrier/endpoints; normal realization does not.

The actual newly allocated variable is applied to fresh local variables
under the shifted telescope. Its original equality typing, full normality,
and transport typing are proved. Replacing the full local transport by the
actual extended identity fill reduces to the LITERAL filled payload;
direct original typing of that application is independent of its reduction.
The exact declaration rank is inherited from ContextualEqualityRealizer.
This is a constructive one-field allocator, not universal enumeration or
full source quotation.

## Reproduction and retained failures

Fresh absolute build directory: `/tmp/pts-rk-contextual-equality-extension.3djfkV`.
Raw local evidence: `_build/contextual-equality-extension.HTcevu`.
Retained RUN.sh/CHECK.sh include exact dates, exit codes, versions and commands.

```sh
cd /Users/akuklev/air/pts-rk
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
timeout 1200 opam exec -- dune build \
  --build-dir=/tmp/pts-rk-contextual-equality-extension.3djfkV \
  --display=short --no-buffer -j 2 \
  theories/self_interpreter/ContextualEqualityExtension.vo
```

Attempt01 exit1: Dune registration pending. Attempt02 exit0: initial fourteen
reports closed. Attempt03 exit1: explicit scope argument to CT.context_sub
was n instead of S n in the new filled-typing wrapper. Attempt04 exit0 after
correcting that argument, all SEVENTEEN own reports CLOSED. No theorem
weakening, timeout, interruption or disk failure.

```sh
timeout 1200 opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-contextual-equality-extension.3djfkV/default/theories PTSrk \
  -Q /tmp/pts-rk-contextual-equality-extension.3djfkV/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-contextual-equality-extension.3djfkV/default/theories/self_interpreter PTSrk.SelfInterpreter \
  PTSrk.SelfInterpreter.ContextualEqualityExtension
```

Recursive kernel exit0. Loaded inventory contains only unchanged upstream
dependent functional extensionality, no unsafe fixpoint, assumed positivity
or type-in-type; this is distinct from the seventeen closed own reports.
Forbidden-declaration scan exit1 (no matches). Aggregate/pristine checking
is a separate later gate. Independent read-only review by the quotation-cache
owner passed: actual equality-only global allocation, original fill typing,
independent realization and literal arbitrary local transport erasure were
checked; no correction requested.

Recorded versions: Rocq9.2.0, Stdlib9.1.0, Equations1.3.2+9.2, OCaml4.14.2,
Dune3.23.1, opam2.6.1. HEAD e822cd62df393faf4d5e4ed0c4c8fed173ccba6f.
CHECK.sh runs git rev-parse HEAD, rocq -v, dune --version, ocamlc -version,
opam --version and opam list --installed --columns=name,version in the same
pinned environment. No final whole-development audit claim is made here.
