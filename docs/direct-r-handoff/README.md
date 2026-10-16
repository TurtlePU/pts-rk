# Proof-development handoff

Start with the newest entry in [STATE.md](STATE.md), then
[DECISIONS.md](DECISIONS.md) and [BUILD.md](BUILD.md). These record actual
compilation, theorem status, design changes, next goals, and exact commands.
The [root README](../../README.md) and [source map](../../theories/README.md)
describe the current layout.

## Current versus historical material

- `STATE.md` and `DECISIONS.md` are append-at-the-top journals. Old entries
  describe earlier stages and may have obsolete paths or unfinished statuses.
- `BUILD.md` is maintained guidance for the current checkout.
- [HANDOFF.md](HANDOFF.md), [LATEST_DECISIONS.md](LATEST_DECISIONS.md), and
  [MATHEMATICS.md](MATHEMATICS.md) preserve the original arithmetic handoff.
  The file called LATEST_DECISIONS is historical; use DECISIONS for live work.
- [inputs](inputs/README.md) contains frozen recovery packages, not patches to
  reapply over installed sources.
- [reference](reference/README.md) contains the original TeX used to identify
  the target by label.
- `verification/` contains exact dated commands and raw compiler/audit logs.
  Their recorded source paths remain unchanged.

The 2026-10-14 layout change moved `Interpretation_of_R/` and `ZFC_model/`
under `theories/` without changing Rocq namespaces or proof source contents.
Prefix old filesystem build targets with `theories/` when running them in the
current checkout; do not rewrite historical raw evidence to look newer.

The arithmetic public theorems are proved. Original set-model soundness is
proved with explicit supplied parameters; its material BZC foundation
reduction remains open. See the relevant source-folder READMEs for precise
boundaries, including normalization's external STLC hardness theorem.
