# Literal catalogue source realization

MM0CatalogueRealization.v compiles in attempt-04, exit 0,
19:18:44–19:18:45 UTC on 2026-10-23, with seven closed assumption reports.
Full recursive kernel checking exits 0 at 19:19:14–19:19:35. Its entire
context inventory matches the previous freshly compiled pristine upstream
inventory after whitespace normalization: inherited
functional_extensionality_dep only, no unsafe items or dependency skips.

The independent fold evaluator is proved complete for Form. Each successful
one of the 17 numerical source-row families constructs an actual original
MM0SyntaxSoundness.Derivation. All 65 catalogue shapes are covered uniformly
in every numerical parameter. The strongest interface is:

```coq
inhabited (Derivation all_axioms (aAx M T)) <->
exists l, M = quote_term (CatalogueEconomy.subject l) /\
          T = quote_term (CatalogueEconomy.declared_type l).
```

This is catalogue/source adequacy, not original-PTS-to-catalogue completeness.
It does not prove full55 finite model existence or internal consistency.

Attempts 01 and 02 exit 1 on a sorting tactic that partially progressed
before handling the conditional substitution row. Attempt 03 passes the
evaluator/sorting lemmas; attempt 04 adds and passes all row realization
theorems. Every attempt retains its exact command, output, exit code and
timestamps. The object directory is /tmp/pts-rk-mm0-realization.8ricsy.

```sh
bash docs/direct-r-handoff/verification/combinatory-mm0-bridge-2026-10-23/realization/CHECK.sh attempt-04
bash docs/direct-r-handoff/verification/combinatory-mm0-bridge-2026-10-23/realization/KERNEL.sh
bash docs/direct-r-handoff/verification/combinatory-mm0-bridge-2026-10-23/computational/FINAL.sh
```

FINAL.sh passes both complete inventories, all 44 new closed reports,
compiled-source equality, source safety and scoped whitespace. Final source
SHA256: ef7d28db8f3a342e9a2bcf859c5b1faadc1b8e3f1541392c8b073bc00257d3d5.
No staging, commits or edits to other proof sources were performed.
