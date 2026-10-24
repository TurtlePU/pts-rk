# Roadmap PDF verification — comparison-preserving execution

## Intermediate build, before the final boundary refinement

Exact build command from the repository root:

```sh
bash theories/self_consistency/build-note.sh DIRECT_ROADMAP
```

Exit 0. Fresh note build directory:
`/tmp/pts-rk-consistency-note.B4XQac`. Build/native TeX logs, versions and
the recorded build exit code are archived in `note-01/`.

Exact inspection commands:

```sh
mkdir -p /tmp/pts-rk-consistency-note.B4XQac/inspection
swift docs/direct-r-handoff/verification/self-consistency-direct-roadmap-2026-10-22/inspect.swift theories/self_consistency/DIRECT_ROADMAP.pdf /tmp/pts-rk-consistency-note.B4XQac/inspection
```

Exit 0: 21 nonempty pages, seven links, required text and mathematics checks
pass, all 21 pages rendered. Extracted text is archived; generated images and
TeX caches are not copied into the repository.

The root agent visually reviewed changed pages 1, 9, 10, 20 and 21. The
comparison-preserving compiler, fixed internal fold, independently generated
synchronous traversal and remaining external compiler/internal soundness
boundary are legible. This is not a proof that every accepted arbitrary
traversal has the intended semantics or a full internal consistency theorem.

SHA256 of the reviewed source and PDF:

```
106620904907e734eedd9f95e68b7eeeed1f5d2de3e467059c07c19cfc885eb8  DIRECT_ROADMAP.tex
571a1dc8bb50712abfb6bf23bbaa0921fe158e5db3708a4ae3156500e508e144  DIRECT_ROADMAP.pdf
```

This successful intermediate build is retained, not presented as the final
note: subsequent review clarified that a total internal compiler is optional
if independent output-neutral resource witnesses have proved standard coverage
and internal checker agreement, without assuming either result in admission.

## Final reviewed build

The same build command succeeds with exit 0 in
`/tmp/pts-rk-consistency-note.k6uAuy`; logs and versions are in `note-final/`.
Exact inspection:

```sh
mkdir -p /tmp/pts-rk-consistency-note.k6uAuy/inspection
swift docs/direct-r-handoff/verification/self-consistency-direct-roadmap-2026-10-22/inspect.swift theories/self_consistency/DIRECT_ROADMAP.pdf /tmp/pts-rk-consistency-note.k6uAuy/inspection
```

Exit 0: 21 nonempty pages, seven links, required text/math checks and all-page
rendering pass. The root agent visually reviewed the final changed pages 10
and 21; previously reviewed content on pages 1, 9 and 20 remains unchanged.
The refined boundary explicitly permits a resource-relative relational route
instead of requiring a total internal compiler, but still requires proved
standard coverage and internal checker agreement independent of admission.

Final SHA256, independently rechecked against the repository:

```
c1a0a46279efcdf8e7a567006416807b6d2cf34569ec99e20519a374d43ae30f  DIRECT_ROADMAP.tex
147e7a7824a499c742d3f8aabf77a230d604b38899f34c9c1d6e3ef70cb9a01a  DIRECT_ROADMAP.pdf
```
