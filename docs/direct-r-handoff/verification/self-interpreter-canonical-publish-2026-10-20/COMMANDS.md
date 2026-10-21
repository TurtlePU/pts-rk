# Canonical milestone publication — 2026-10-20

Continuation confirmation: the pending ordinary push (exec session 20431)
completed with exit 0, advancing origin/main from b6c81d1 to
e822cd62df393faf4d5e4ed0c4c8fed173ccba6f. Independent
`git ls-remote origin refs/heads/main` confirms the latter full hash, equal
to root main. The Keychain pause is resolved. No subsequent continuation
changes are included in that already completed publication.

Prepared at the user's explicit commit/push request from main
b6c81d1c24404835f5665b8bf4c263379dee5202 in the already isolated, clean
/tmp/pts-rk-phoas-publish.x7qwoT/worktree. Only the four canonical modules,
self-interpreter Audit/Dune/README, note/PDF, concise canonical evidence and
scoped STATE/DECISIONS/BUILD additions are included. Unrelated root changes
are excluded. No source or CI rule is weakened.

The proof hashes exactly match the preceding
[canonical checkpoint](../self-interpreter-canonical-2026-10-20/COMMANDS.md).
Fresh independent publication audit exits 0 with **326 closed reports**.
All nine recorded stages pass: fresh build, recursive original and aggregate
kernel checks, byte-identical pristine core inventory, frozen reference ZFC,
original kernel and normalization-source comparisons, shell syntax, and
source stability. Only unchanged upstream functional_extensionality_dep is
in the recursive loaded-context inventory; no unsafe/check bypass is added.

Raw evidence and literal runner:
/tmp/pts-rk-canonical-publish.ByVRjo/AUDIT.sh.
Fresh absolute build directory: /tmp/pts-rk-canonical-publish-build.80zkDC.
The runner exports the pinned PATH/OPAMROOT/OPAMSWITCH, uses timeout 1200,
and records each exit status separately. Exact principal commands:

```sh
bash /tmp/pts-rk-canonical-publish.ByVRjo/AUDIT.sh
opam exec -- dune build --build-dir=/tmp/pts-rk-canonical-publish-build.80zkDC --display=short --no-buffer -j 2 @theories/self_interpreter/audit
opam exec -- rocq check -silent -o -Q /tmp/pts-rk-canonical-publish-build.80zkDC/default/theories PTSrk -Q /tmp/pts-rk-canonical-publish-build.80zkDC/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-canonical-publish-build.80zkDC/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.Audit
```

Versions are Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1, opam 2.6.1. No compiler failure or timeout.
The prior root-worktree CI has 226 passing stages; the previously published
snapshot has 172. This fresh scoped audit is not a new full CI or remote CI
claim. Original raw checkpoint logs retain their original paths and Git states.

The note source is unchanged from the checked checkpoint. The PDF was
regenerated externally before this publication request, so its old byte hash
and old build-size assertion are not transferred to the new file. Actual
publication hashes:

```text
f8ea4a625231ad49e1e1e931385d16ea4f7b1e1183ae584dd290c5cca28757b3  PTS-rk_self_interpreter.tex
861d0d4b7e28d0afd216b73412c925c5bb155ad857814cd4ac72d0e8d6a08719  PTS-rk_self_interpreter.pdf
```

Current PDFKit inspection confirms 20 pages, 274101 bytes. All-page text and
page8.png are retained in the raw evidence directory; the actual canonical
substitution theorem page was visually inspected and renders correctly.

Root index and all pre-existing tracked/untracked nonignored file hashes
are backed up as root-index-before and root-before.sha256 in the raw directory.
The publication uses an ordinary commit and non-force push. Subsequent root
branch/index synchronization must not rewrite working-tree files; the root
handoff records the final commit and remote confirmation. The mathematical
boundary remains an executable full-PTS METALEVEL canonical algebra, not an
internal dependent PHOAS evaluator. New object-language work follows the push.
