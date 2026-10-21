# Scoped capped-fragment publication and disk cleanup

2026-10-21. Starting HEAD: 1d1f2462b1d5dff9f94f8f1f3247f40d34769a90.
The user explicitly requested commit, ordinary push and cache cleanup.
No proof, manuscript or PDF changes were made during publication.
Prior compilation/kernel/CI evidence is recorded in the two preceding
fragment-uniformity and capped-quotation checkpoints, not rerun here.

Publication-time `bash .../self-interpreter-capped-quotation-2026-10-21/FINAL-CHECKS.sh`
revalidated all 123 hashes and preceding kernel/CI conditions, then exited 2
at `git diff --check`: CappedCodeAlignment.v has an extra EOF blank line.
The audited bytes are retained. This is not a new proof-check failure.

Inspections: git status/diff/index/remotes; ps (no active Rocq/Dune builds);
du sorted external cache sizes; explicit .db/default checks before cleanup.
Using the pinned PATH/OPAMROOT/OPAMSWITCH from BUILD.md, each command
`opam exec -- dune clean --build-dir=TARGET` exited 0 for these exact targets:

```
/private/tmp/pts-rk-capped-audit.lpDpbN
/private/tmp/pts-rk-quotation-cache.ddlOA9
/private/tmp/pts-rk-checked-contextual.vLMi7j
/private/tmp/pts-rk-bzc-numerals.odd7Cz
/private/tmp/pts-rk-bzc-sort.RTSnx1
/private/tmp/pts-rk-bzc-leaves-choice.27UiOL
/private/tmp/pts-rk-bzc-split.VAAGHc
/private/tmp/pts-rk-bzc-baseline.Ce548l
/private/tmp/pts-rk-contextual-beta.Pp1d1l
/private/tmp/pts-rk-graph-beta.v7gRB2
/private/tmp/pts-rk-telescope-beta-family.B7M4Iw
/private/tmp/pts-rk-self-scoped-tarski.qA1Bug
/private/tmp/pts-rk-tarski-beta-signature.3vggOl
```

These are regenerable compiled artifacts, not source checkouts. Raw evidence
under the repository's _build, the current _build/default, toolchain and all
source changes were retained. Available filesystem space from `df -k .`:
398964 KiB before; 2807888 KiB after (2408924 KiB reclaimed, about 2.3 GiB).
Historical fresh-build paths now name cleaned caches, not extant proof binaries.

Publication scope: self_interpreter sources/Dune/Audit/README/OBLIGATIONS,
note and PDF, the two previous evidence directories, this record, and only
the newest relevant prefixes of shared STATE/DECISIONS/BUILD. Shared-file
index blobs are constructed from those prefixes plus their HEAD remainder;
the worktree and all unrelated hunks are untouched.
Ordinary publication commands: git commit with the scoped index;
git push origin main; git ls-remote origin refs/heads/main to confirm.
