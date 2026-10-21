# Canonical source derivations with typed forward conversion certificates

Date: 2026-10-21. Working directory: `/Users/akuklev/air/pts-rk`.
Owned source: `theories/self_interpreter/CanonicalSource.v`, 155 lines.
SHA-256: `0ab23ea3ba216deccdd18afa9045df93cc7eed5233e765fd253a9c7e264523f2`.
This subtask edits only the new source and scoped evidence. The coordinator
owns Dune/Audit/prose/handoff integration. No frozen source, original kernel,
Git index or reference was modified.

## Constructive contract

The six `derivation` constructors retain the literal original context,
term, type, lambda annotation, product rank and variable lookup. Conversion
now carries `FullConversion.joining`: two actual forward chains to a common
term. The datatype does NOT assume its `certified` property, any target
quotation, or source-normalization result. Its original typing soundness
does not require context well-formedness.

`canonical_join` computes `join_attempt` on the conversion's two source
types. On success it returns the actual computed joining plus the exact
success equation. Only in the impossible failure branch does it eliminate
the Prop existential rank supplied by original `type_is_correct`, using
the independently supplied source derivations, original conversion and
`join_attempt_complete` to obtain False. No proof in Prop is inspected to
construct a reduction/derivation constructor or select a computational rank.

`canonicalize` is a transparent structural recursion on SUPPLIED FullSource
data, with an original well-formedness witness for the input context. It
reuses the literal judgment indices and replaces each conversion certificate
by the computed joining. Product/lambda recursion constructs original child
well-formedness from the domain's independent source derivation. It does not
normalize or erase any source annotation, term, type or context declaration.

`canonicalize_certified` proves recursively that every conversion's common
endpoint is normal and every stage of both forward traces has original
typing. The left formation rank is existential in Prop; the right rank is
the source conversion rule's explicit target sort. Full original coverage
in well-formed contexts follows from FullSource's inhabited completeness:
every such original typing has certified canonical data. This remains a
Prop existence theorem, not extraction of source evidence from opaque typing.
Arbitrary invalid-context coverage is not asserted for canonicalization.

This module changes source evidence, not the object-language representation.
It neither supplies internal Tarski conversion witnesses nor proves a full
dependent quoter. Its successful executable joining is established from
original source typing; no desired target conclusion is a domain premise.

## Verification and exact commands

Fresh absolute Dune directory: `/tmp/pts-rk-canonical-source.dRksqw`.
Ignored raw evidence: `_build/canonical-source.F2ZxuI/`.
Final compile exits 0 with EIGHT closed module assumption reports.
Independent read-only review passes all domain, original typing, recursion
and Prop/Type-boundary checks; no correction was requested.
Recursive kernel checking exits 0. The loaded inventory contains only the
unchanged upstream functional-extensionality declaration; there is no unsafe
fixpoint, type-in-type or assumed positivity. This loaded inventory is
separate from the eight closed theorem-level reports.

Every attempt uses `bash _build/canonical-source.F2ZxuI/RUN.sh NN`.
The retained runner is exactly:

```sh
#!/usr/bin/env bash
attempt="$1"
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-canonical-source.dRksqw --display=short --no-buffer theories/self_interpreter/CanonicalSource.vo > "_build/canonical-source.F2ZxuI/attempt-$attempt.log" 2>&1
build_status=$?
printf '%s\n' "$build_status" > "_build/canonical-source.F2ZxuI/attempt-$attempt.exit"
tail -45 "_build/canonical-source.F2ZxuI/attempt-$attempt.log"
exit "$build_status"
```

| Attempt | Exit | First outcome |
| --- | --- | --- |
| 01 | 1 | Target not yet registered by the coordinator. |
| 02 | 1 | Destructing join_attempt had already rewritten the Some-branch equality; reflexivity closes it. |
| 03 | 1 | Application constructor could not infer its domain from the substituted result type. |
| 04 | 1 | Named tactic application did not expose implicit constructor indices; use explicit constructor application. |
| 05 | 1 | A theorem's unused wf binder needed an explicit type annotation. |
| 06 | 0 | Entire final module compiles, eight closed reports. |

The final source build reruns its reports, not a cached no-op. No timeout,
theorem weakening or disabled check/warning occurred. The known loadpath
remapping warning remains visible in the retained logs.

Version command (exit 0, `versions.log`/`.exit`):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune > _build/canonical-source.F2ZxuI/versions.log 2>&1
version_status=$?
printf '%s\n' "$version_status" > _build/canonical-source.F2ZxuI/versions.exit
sed -n '1,30p' _build/canonical-source.F2ZxuI/versions.log
exit "$version_status"
```

Actual versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2 and Dune 3.23.1.

Recursive kernel command, retained in `CHECK.sh` with `kernel.log` and
immediately captured `kernel.exit`:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-canonical-source.dRksqw/default/theories PTSrk -Q /tmp/pts-rk-canonical-source.dRksqw/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-canonical-source.dRksqw/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.CanonicalSource > _build/canonical-source.F2ZxuI/kernel.log 2>&1
kernel_status=$?
printf '%s\n' "$kernel_status" > _build/canonical-source.F2ZxuI/kernel.exit
tail -30 _build/canonical-source.F2ZxuI/kernel.log
exit "$kernel_status"
```

Scoped whitespace checking exits 0; the search for admissions, axioms,
disabled checks and diagnostic Show has no matches (expected rg exit 1).
Source hashing uses `shasum -a 256`. Aggregate/pristine checks and full CI
remain the coordinator's separate verification, not implied by this build.
