# Build and CI tools

Run these scripts from the repository root. None requires GitHub CLI.

| Script | Purpose |
| --- | --- |
| `check-local-ci.sh` | Select the dedicated local opam switch, validate the workflow with actionlint, run the complete CI driver |
| `ci-check-direct-r.sh` | Build an isolated pristine upstream snapshot, then normalization, arithmetic, and set-model modules; stop at the first failure |
| `check-direct-r.sh` | Smaller functional smoke check in an already activated Rocq/Equations environment; not the complete audit |
| `build-markdown-paper.sh` | Fresh LuaLaTeX/Biber paper build, source/rendered checks, copy successful review PDF |
| `build-development-docs.sh` | Fresh LuaLaTeX builds of all five finished-development expositions; publish PDFs only after all pass reference, glyph and overflow checks |
| `check-markdown-paper.py` | Compare Markdown/traditional paper body and ordered mathematics; optionally inspect parser output |
| `check-markdown-class.sh` | Compile four date/author-layout metadata regression fixtures using the local class/runtime |

See [DirectR-CI.md](../docs/DirectR-CI.md) for pinned versions and setup.
The script names and `DIRECT_R_*` environment variables are retained for
compatibility although the complete driver now covers all developments.

```sh
bash tools/check-local-ci.sh
# In an already activated opam switch:
opam exec -- bash tools/ci-check-direct-r.sh
bash tools/check-direct-r.sh
```

`DIRECT_R_LOG_DIR` selects the diagnostic directory; the local wrapper defaults
to ignored `_build/local-ci-logs/`. `DIRECT_R_JOBS` controls Dune concurrency
(default 2), and `DIRECT_R_STAGE_SECONDS` sets each stage's diagnostic timeout
(default 1200). The full driver also accepts `DIRECT_R_BASELINE_REF`, defaulting
to the documented original kernel commit.

Logs include commands' compiler output, stage exit codes, tool versions,
resolved opam packages, and Dune logs. Timeouts and interrupted runs remain
failures. Fresh assumption output requires fresh compilation, not a cached
target. The wrapper validates workflow syntax but does not emulate GitHub
setup, checkout, or artifact upload actions.
