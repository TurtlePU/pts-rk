# Full-PTS canonical contexts and hereditary type indices — 2026-10-20

This is new, uncommitted work after the requested publication, merge and push.
The source library remains PTSrk.SelfInterpreter. Original PTS syntax, rules,
annotations, conversion, normalization sources and the frozen ZFC model are
unchanged. No new axiom, admission, unsafe cast or disabled check is used.

## Publication and worktree boundary

Committed the preceding finite-PHOAS snapshot as
3411f31f007caecfe5251dacb276583edbd4bba9, merged docs/finished-developments
at 6820469a75acf5a1adda248c193930a9b22daa6a by the actual two-parent merge
64864e36b4d748cf117f830cdc4438d4d4054a2f, and committed clean verification
as b6c81d1c24404835f5665b8bf4c263379dee5202. Ordinary push succeeded;
git ls-remote origin refs/heads/main confirms the latter tip. Root main is
also at that tip, with no staged content. These commits exclude unrelated
pre-existing BZC work and bulky raw logs. All 3576 pre-existing working-tree
files passed byte-preservation checks when synchronizing the branch/index.
See [the publication record](../self-interpreter-publish-2026-10-20/COMMANDS.md).

The clean published snapshot passes **172/172** stages. The subsequent root
workspace, including unrelated unpublished developments, passes **226/226**.
These are different source snapshots; neither number is a remote CI claim.
No new canonical proof work was included in the earlier push.

## Proved milestone

OpenCanonical computes a sufficient open-context budget directly from
context/term syntax and proves full normalization from independent original
wf/typing. CanonicalSubstitution proves typed hereditary substitution,
normalization of both terms and dependent result types, identity, composition
and conversion coherence. CanonicalContexts constructs normalized original
contexts, actual identity TypedSub in both directions, literal same-term/type
typing equivalence, normality, idempotence and original context reduction.
CanonicalTypeIndex separates faithful raw syntax codes from canonical type
indices identifying exactly beta conversion on independently typed inputs.

The checked regression substitutes a normal lambda for f in the normal
original type f U0 and creates a beta redex. Thus normalization after
substitution is not dispensable. The separate faithful code still preserves
exact original annotations; canonical type indices do not claim injectivity
of unreduced source syntax.

These executable metalevel results apply to **full dependent original PTS**,
not merely the independent STLC source. They supply no internal El, dependent
family translation, code-to-value reifier or full dependent PHOAS evaluator.
The strong closed PHOAS decoder still has the independent STLC source and
external indices (budget, full simple type). Full dependent PHOAS is not
ruled out. The next goal is to realize the distinct syntax/canonical-index
interface inside original PTS, constructing represented dependent families
and typed reification with coherence, without assuming those target laws.

## Verification

All module attempts, including failures and their resolutions, are retained:

- [Open-context normalization](open-normalization/COMMANDS.md).
- [Hereditary substitution](substitution/COMMANDS.md).
- [Canonical contexts](contexts/COMMANDS.md).
- [Canonical type indices](type-index/COMMANDS.md).
- [Independent contract review and final audit](final-review/COMMANDS.md).

The final audit uses fresh absolute Dune directory
/tmp/pts-rk-self-canonical-audit.JWgIgs and raw ignored evidence directory
_build/self-interpreter-canonical-final-review.TPZ60J. It exits 0 with
**326 closed reports**: 228 module, 97 aggregate and one core. The four new
modules add 10 + 8 + 10 + 15 = 43 reports, with 19 new aggregate endpoints.
Recursive kernel checks pass; original-core inventory is byte-identical to
pristine upstream. Only unchanged upstream functional_extensionality_dep
appears in the recursive loaded-context inventory. Unsafe, type-in-type and
assumed-positivity inventories are empty. Frozen ZFC, original core and
NormalizationComplexity source comparisons are empty. All 226 local CI
stages and actionlint pass. No final audit/CI timeout or error occurred.
Exact commands, timestamps and pinned tool versions are in the final report.

Final frozen proof/integration hashes:

```text
155c091012d3251a3ea083100caec60fef1d567fe86bcb6fe4b0d0b38ccc0889  OpenCanonical.v
1a3e89fb34d28c816e5a95b423d252d373a3ad2ae7e51c68226a67445acf6ed4  CanonicalSubstitution.v
0f3e33864857fe81c2eb114b0c08022ca3ffb11ec3439db91676a95546e3b858  CanonicalContexts.v
c161417c3e65e985d9d46bee6af9c9402f4297a49b24186487115e9e2a1358fa  CanonicalTypeIndex.v
627dda73332768c24923a08bc33ffee3b8337b116967264aa43fb3acc162929d  Audit.v
ea681a30cee9122bc238c3152178ae7fd92fa6c036efcec15a5d742a96921ca6  dune
```

## Note and PDF

The LaTeX–Markdown note now includes the executable open bound, the full-PTS
hereditary substitution theorem, context typing equivalence, canonical-index
equations, checked redex regression and explicit object-language limitations.
Independent prose review checked all equations against the frozen APIs.

```sh
bash tools/build-self-interpreter-note.sh
shasum -a 256 PTS-rk_self_interpreter.tex PTS-rk_self_interpreter.pdf
```

Initial build /tmp/pts-rk-self-note.vIKx3l exits 0: 20 pages, 270639 bytes.
After the review's precision edit ('full-PTS interpretation result'), final
build /tmp/pts-rk-self-note.zjmn3r exits 0: **20 pages, 270656 bytes**.
Both use latexmk 4.88 and LuaHBTeX 1.24.0 / TeX Live 2026. No overfull boxes,
missing glyphs or unresolved references; three mild underfull boxes with
badness 1314, 2111 and 1629. Final all-page PDFKit text is retained there as
pdf-text.txt. Pages 8, 9 and 20 were rendered to PNG and visually checked:
the theorem, normalized context/index equations and final scope render cleanly.

```text
f8ea4a625231ad49e1e1e931385d16ea4f7b1e1183ae584dd290c5cca28757b3  PTS-rk_self_interpreter.tex
8b60d56e4c14bcfacdb3f51f20effdaa1c9d081dc5942eabb31c3a91edbc70c9  PTS-rk_self_interpreter.pdf
```

The new proofs, note/PDF and handoff changes remain uncommitted, separate
from the completed requested publication. No unrelated user work was removed.
Final scoped git diff --check and git diff --cached --exit-code exit 0.
For the four untracked proof files and two new parent-authored evidence files,
git diff --no-index --check /dev/null FILE emits no whitespace diagnostics;
its exit 1 denotes the new-file difference, not a compiler/check failure.
An initial shell loop treated that expected exit 1 as a stop; the checks were
then run individually. Final proof and note/PDF hashes remain as listed above.
