# Shared algebra, PHOAS folds and numeral-free combinatory CPS

## Scope

Eight new files: seven proof modules (`Algebra`, `GenericFold`,
`UnifiedAlgebra`, `PHOASFold`, `PHOASCPS`, `CombinatoryFold`,
`CombinatoryAlgebra`) and `FoldAudit` with 106 public Check/Print pairs.
Dune registers the common API, the concrete
combinatory dependency and a focused fold-audit alias; the original audit
alias retains both the new and compatibility audits. No original kernel,
normalization, combinatory-development, arithmetic or set-model source changed.

The complete self-interpreter README is streamlined from 1086 to 183 lines;
its older milestones are represented by current contracts and source modules,
not repeated as unfinished work. The research note is reorganized around
the shared algebra and concrete folds. The consistency note records the
structural-code bridge without claiming internal soundness.

All prior dirty/intent-to-add work is preserved. HEAD at start is
cb76553b03d536743e36c4e2c7e5a1c7c1669bef. No Git staging, commit or push was
requested or performed by this continuation.

## Contracts

- The shared fold is actual original application of a program to a typed
  telescope filling. Exact adapters preserve existing STLC and combinatory
  codes. Both dependent type and term programs use the same algebra.
  `GenericFold` has one actual normal head per signature, receiving type,
  term and algebra fields as ordinary arguments; it embeds no selected
  filling. Its nested-run equation is syntactic computation, not semantic
  fusion or arbitrary-interface type compatibility.
- Tag-free full-dependent identity interpretation recovers the literal
  original term/type and retains original typing and normal codes/heads.
  Its generic normal-source fidelity uses a COMMON algebra. The old faithful
  envelope remains for arbitrary reducible-source/cross-plan syntax fidelity.
- The STLC constructor observer is a complete nonidentity filling of the
  existing palette. Its output is a distinct exact-rank sort token, not an
  internally eliminable Boolean. A typed beta example proves non-invariance
  under source conversion.
- The CBN operations and structural CPS types are originally typed, with
  administrative beta equations and exact ranks. Unbounded target rank at
  source order one concerns that literal translation, not every CPS encoding.
- Binder-free finite-dictionary codes have formation rank r+2, intrinsic
  tree fidelity, internal folds and a typed CBV continuation algebra. A
  finite Boolean observer consumes the SAME rank-correct code. The concrete
  65-shape catalogue bridge is extraction/coding, not dependent unquotation
  of heterogeneous expansions or native PTS completeness.

A single rank-fragment dependent signature, full dependent nonidentity
coherence/CPS, intrinsic all-source payload parsing and internal accepted-
certificate soundness remain open. No numeral conversion is used by these
folds; external resource indices and arithmetic-coding obligations remain.

## Fresh audit

Exact reproducible command:

```sh
bash docs/direct-r-handoff/verification/self-interpreter-fold-2026-10-22/AUDIT.sh
```

Pinned environment: Rocq 9.2, Stdlib 9.1, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1. Full installed versions and escaped commands,
UTC starts/ends, exit codes and raw stdout/stderr are retained in
`_build/self-interpreter-fold-audit.7pRHdb`.

Fresh absolute build: `/tmp/pts-rk-fold-fresh.VfFDz4`.
Independently rebuilt pristine snapshot: `/tmp/pts-rk-fold-pristine.tRiUN0`,
commit 723cf2ec61c737ae82ba33d2e7db44f650122b0e.
Pristine build/kernel exit 0 (11:09:16–11:09:25 UTC).
Fresh new-module dependency closure exits 0 (11:09:25–11:14:37 UTC),
1169 closed reports including dependencies. Separate fresh FoldAudit exits 0
(11:14:37–11:15:07 UTC), exactly 92/92 closed public reports, no axioms.
Recursive FoldAudit kernel check exits 0 (11:15:07–11:19:55 UTC).
The first raw-log comparison exits 1: the development's harmless logical-
loadpath warning precedes its inventory, unlike the pristine log. The
harness now extracts each COMPLETE nonempty CONTEXT SUMMARY through EOF;
these inventories compare byte-for-byte. Raw diagnostics are retained.
The exact resume command was:

```sh
bash docs/direct-r-handoff/verification/self-interpreter-fold-2026-10-22/AUDIT.sh --finish /Users/akuklev/air/pts-rk/_build/self-interpreter-fold-audit.7pRHdb /tmp/pts-rk-fold-fresh.VfFDz4 /tmp/pts-rk-fold-pristine.tRiUN0
```

Inventory comparison and original-kernel identity exit 0 at 11:21:22 UTC.
The full development's compatibility audit builds successfully,
11:21:22–11:32:11 UTC, followed by source-stability and whitespace exit 0.
This focused audit is not a new full-repository CI claim.

## Ordinary-argument generic fold extension

GenericFold was developed outside the repository until the above source-
stability check finished. Its 14 endpoints and the exact failure/fix are
recorded in [GENERIC.md](GENERIC.md). It was then copied byte-for-byte and
registered in Dune/FoldAudit, raising the public total to 106. Exact command:

```sh
bash docs/direct-r-handoff/verification/self-interpreter-fold-2026-10-22/GENERIC-AUDIT.sh /Users/akuklev/air/pts-rk/_build/self-interpreter-fold-audit.7pRHdb /tmp/pts-rk-fold-fresh.VfFDz4
```

First harness attempt at 11:33:54 UTC stopped before compilation: BSD sed
does not implement the chosen basic-regex alternation, so the manifest
filter retained the explicitly expected FoldAudit/Dune/new-file changes.
The exact diff showed only those changes. Switched to portable extended
regex; retained the complete attempt in the raw `generic-initial` directory.
No proof statement or check was weakened.

Final extension starts 11:34:15 UTC. Every prior dependency source matches
the source-stable manifest. GenericFold fresh compilation exits 0 at
11:34:16; separate fresh FoldAudit exits 0 at 11:34:46 with **106/106**
closed reports. Recursive GenericFold kernel check exits 0 at 11:35:00;
its entire context inventory again equals pristine. Together with the
prior recursively checked, unchanged closure this covers every new module.
The only imported axiom in both inventories is unchanged upstream
`functional_extensionality_dep`; no type-in-type, unsafe fixpoints or
assumed positivity. Final working compatibility audit exits 0,
11:35:00–11:35:31 UTC, followed by source-stability and whitespace exit 0
in the adjacent raw `generic/status.tsv`.

The main AUDIT.sh now reproduces all seven modules and 106 endpoints in
one fresh run; this continuation used the two explicitly recorded stages.

Incremental failures, exact direct-compiler commands, final hashes and narrow
kernel checks are recorded in [ALGEBRA.md](ALGEBRA.md),
[COMBINATORY.md](COMBINATORY.md), and the retained
`_build/phoas-fold-design/COMMANDS.md` and adjacent logs. Intermediate
diagnostic successes with aborted lemmas are explicitly not counted as
completed proofs. Final sources contain no admissions/axioms/unsafe flags.

## Documents

`bash theories/self_consistency/build-note.sh` exits 0 in
`/tmp/pts-rk-consistency-note.7vQRc9`: 10 pages, no overflow/underflow,
reference or missing-glyph diagnostics. The new `inspect.swift` exits 0,
checks required text and renders all pages. The added passage on page 7 was
visually inspected. Raw logs/renders are in the main audit directory.
SHA256 values are recorded in `theories/self_consistency/EVIDENCE.md`.

The interpreter note is reduced from 1044 lines/15 pages to 682 lines/10
pages. Final build exits 0 in `/tmp/pts-rk-self-note.a3CRxJ`, with no layout,
reference, missing-glyph or malformed-math warnings. All six builds,
intermediate corrections and final hashes are in [NOTE.md](NOTE.md).
The independent `inspect.swift` exits 0: ten nonempty rendered pages,
required discussion text and the Brown–Palsberg primary citation link.
Pages 2, 3, 5, 7 and 10 were visually inspected, including the generic-head
formula, CPS examples and comparison; no clipping or raw TeX observed.

```sh
mkdir -p _build/self-interpreter-fold-audit.7pRHdb/interpreter-pdf
swift docs/direct-r-handoff/verification/self-interpreter-fold-2026-10-22/inspect.swift PTS-rk_self_interpreter.pdf _build/self-interpreter-fold-audit.7pRHdb/interpreter-pdf interpreter
```

## Final scope check and temporary-cache cleanup

Shell syntax checks pass. Final scoped `git diff --check` exits 0 for the
changed development, notes, root README, handoff files and this verification
directory. A broader check also including historical verification directories
exits 2 on pre-existing raw combinatory command/TeX logs with whitespace;
those unrelated evidence files were left untouched. Both complete outputs
and exit codes are retained as `broad-whitespace.*`/`final-whitespace.*`.
The final inspector additionally checks every page has nonempty text and
the interpreter PDF includes GenericFold; both ten-page PDFs pass.

After all checks, validated the exact newly created temporary directories,
their expected compiled/snapshot files and absence of active compiler jobs.
Removed ONLY `/tmp/pts-rk-fold-fresh.VfFDz4` (326960 KiB) and
`/tmp/pts-rk-fold-pristine.tRiUN0` (2084 KiB): about 321 MiB of reproducible
audit outputs/snapshot, not user sources or general caches. The environment
rejected a force-removal invocation before execution; ordinary `rm -r`
without force succeeded, exit 0. Exact size/time/status remain in
`cleanup-*`/`cleanup.exit` in the main log directory. All audit logs,
source manifests and document renders remain. The main AUDIT.sh recreates
fresh directories; the historical two-stage extension command requires its
original baseline and is not a resume command after cleanup.
