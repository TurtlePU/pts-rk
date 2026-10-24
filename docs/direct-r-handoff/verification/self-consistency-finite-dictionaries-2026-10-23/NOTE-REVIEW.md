# Roadmap PDF verification — fixed dictionary interface

Exact build command from the repository root:

```sh
bash theories/self_consistency/build-note.sh DIRECT_ROADMAP
```

Exit 0. Fresh note build directory:
`/tmp/pts-rk-consistency-note.QJT5ss`. Build log, native TeX log, versions and
the recorded build exit code are archived in `note/`.

Exact inspection commands:

```sh
mkdir -p /tmp/pts-rk-consistency-note.QJT5ss/inspection
swift docs/direct-r-handoff/verification/self-consistency-direct-roadmap-2026-10-22/inspect.swift theories/self_consistency/DIRECT_ROADMAP.pdf /tmp/pts-rk-consistency-note.QJT5ss/inspection
```

Exit 0: 20 nonempty pages, seven links, required text and mathematics checks
pass, all 20 pages rendered. Extracted text is archived; generated images and
TeX caches are not copied into the repository.

The root agent visually inspected changed pages 1, 7, 8, 9, 19 and 20. Formulae,
exact padding ranks, boundary between the internal consumer and external branch
generation, and updated work packages are legible without clipping. No
toolchain warnings, unresolved-reference/missing-character diagnostics or
overfull boxes were reported by the final validation.

Final SHA256:

```
9c8a4020621e700aeb6339e86bee8f64b73f96b8a13efb3f186bdfc0a1c7fbe3  DIRECT_ROADMAP.tex
c2aa306d7ebe8b60ac1c6cb0e0d38e9e662a06665d6094c22e16910378ce20e6  DIRECT_ROADMAP.pdf
```
