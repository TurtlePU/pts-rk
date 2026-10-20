# Expositions of the finished developments

These documents explain the infrastructure, theorem statements, proof
strategy, crucial arguments and limitations of each finished AI-assisted
Rocq development. Each source uses the repository's LaTeX–Markdown dialect,
as in [PTS-rk.tex](../../latex/PTS-rk.tex), and has a compiled PDF.

| Development | Source | PDF |
| --- | --- | --- |
| Shared arithmetic infrastructure | [README.tex](../../theories/Interpretation_of_R/README.tex) | [README.pdf](../../theories/Interpretation_of_R/README.pdf) |
| Relational arithmetic R | [README.tex](../../theories/Interpretation_of_R/relational/README.tex) | [README.pdf](../../theories/Interpretation_of_R/relational/README.pdf) |
| Functional arithmetic R | [README.tex](../../theories/Interpretation_of_R/functional/README.tex) | [README.pdf](../../theories/Interpretation_of_R/functional/README.pdf) |
| Normalization complexity and STLC reduction | [README.tex](../../theories/NormalizationComplexity/README.tex) | [README.pdf](../../theories/NormalizationComplexity/README.pdf) |
| Reference set model | [README.tex](ZFC_model/README.tex) | [README.pdf](ZFC_model/README.pdf) |

The set-model exposition lives here because the entire reference directory
`theories/ZFC_model` is frozen at PR #1 revision `ffa7131`. Its source and
existing documentation remain byte-for-byte unchanged. The new exposition
describes the completed supplied-model theorem and explicitly distinguishes
the ongoing BZC foundation reduction.

The original handwritten kernel is described by the main paper. The unfinished
`BZC_model` and `self_interpreter` developments are outside this documentation
pass; their existing documentation and proof work are preserved.

## Rebuild

From the repository root:

```sh
bash tools/build-development-docs.sh
```

The script requires LuaLaTeX, latexmk, the TeX packages used by
[development-preamble.tex](../../latex/tex/development-preamble.tex), and
ripgrep. It uses the pinned local Markdown runtime, creates a fresh temporary
build directory and retains its logs. It checks every document for missing
glyphs, undefined references and overflowing boxes before copying any PDF
back into the repository. No intermediate LaTeX files are generated beside
the sources. The script prints the build location and output paths.

Proof compilation is separate. Use the pinned toolchain and commands in
[DirectR-CI.md](../DirectR-CI.md). New assumption reports require a fresh
absolute Dune build directory. See the newest
[handoff entry](../direct-r-handoff/STATE.md) for actual verification of
this documentation pass; the mathematical scope of a theorem is always
its live Rocq statement, including its explicit premises.

## Repository hygiene

Generated Python bytecode, solver caches and Markdown parser sidecars are
ignored. Obsolete instances found during this pass were moved into an
ignored local recovery directory, recorded in the handoff. Existing proof
tests, local build copies, dated verification logs and original recovery
packages remain: these provide regression coverage or provenance, and old
log paths are part of the recorded evidence. Historical obligations and
recovery notes are explicitly historical, not instructions to replace the
current sources.
