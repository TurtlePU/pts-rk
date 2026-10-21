# Finite rank-vector contextual beta signature — 21 October 2026

Base commit `e822cd62df393faf4d5e4ed0c4c8fed173ccba6f`.
Own source: `theories/self_interpreter/TelescopeBetaSignature.v`.
Parent owns Dune/Audit/shared prose. No Git/index mutation or edits to
frozen dependencies. The full concrete uniform-family integration is compiled
and frozen, with all 30 own assumption reports closed.

## Checked contract

Descriptors contain ONLY a rank vector of length at most L with entries at
most k, and a,b,d at most k. An executable list lookup and mixed-radix
encoding cover every such descriptor. Every arbitrary finite vector/triple
is covered at its computed length and maximum rank. The number of fields is
exactly ContextualBudgets.count L k times `(k+1)^3`. There is no enumeration
of concrete source syntax or dependent telescope annotations.

The actual context appends UniformContextualBeta families to the existing
TarskiBetaSignature. Original well-formedness, normal declarations, exact
bounded lookup typing, and an actual inherited TarskiContext.environment
are proved. Every descriptor has an actual typed field at its computed
length/rank ceilings. Actual independently typed normal identity_family
programs construct TypedSub into every ambient original context; literal
field recovery, inherited local-beta recovery and replacement naturality
are checked. Declaration formation ranks are bounded numerically by k+3;
this is not a new cumulative typing rule or a full translated-source budget.

The closed-context package has original typing and guarded normality. Its
actual applications have direct original typing and reduce to the literal
identity replacement of their body. This generic telescope application is
not a claim that arbitrary supplied concrete domains have already been
specialized in every contextual witness, nor a full source interpreter.

## Exact commands and failures

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
timeout 1200 opam exec -- dune build \
  --build-dir=/tmp/pts-rk-telescope-beta-signature.p1q5kv \
  --display=short --no-buffer -j 2 theories/self_interpreter/TelescopeBetaSignature.vo
```

Ignored local-only raw evidence: `_build/telescope-beta-signature.pWomgH/`,
including RUN.sh, VERSIONS.sh, versions.log, status.tsv and every attempt.
Versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1, opam 2.6.1; full installed package inventory retained.

| Attempt | Exit | Result |
| --- | --- | --- |
| 01 | 1 | Dune target registration pending; no theorem was checked. |
| 02 | 1 | Filesystem exhaustion during dependency scan/build: `No space left on device`. |
| 03 | 1 | First real proof error: implicit Forall predicate left the descriptor-budget arithmetic underconstrained. |
| 04 | 0 | Explicit source bound fixed that proof; all six descriptor-layer reports closed. |
| 05 | 1 | Dependency TelescopeBetaFamily was still developing its final specialization proof; no own theorem failure. |
| 06 | 0 | Frozen family/wrapper dependencies and full integration compile; all 30 own reports closed. |

The parent removed ONLY validated old generated Dune caches
`/tmp/pts-rk-self-coherence-audit.mM2Zir`,
`/tmp/pts-rk-self-conversion-audit.SRZ7pU`, and
`/tmp/pts-rk-self-binder-congruence.tkK21j` to recover disk space.
Its initial recursive-force removal request was tool-policy rejected with
no action; subsequent ordinary recursive removals succeeded. Historical raw
logs and tracked evidence were preserved; those historical cache paths no
longer designate retained build artifacts. Current-phase caches were kept.
No proof rule, theorem contract or CI check was weakened to address either
the disk failure or arithmetic proof error.

Independent read-only review of the exact frozen source passed: rank-vector
descriptors, executable lookup, computed coverage, context formation,
normality, independently inhabited identity fill, literal closure/run
contracts and explicit boundaries. The inherited S k carrier range correctly
contains c=max(a+1,b). No target-quoter or global-coherence premise appears.

Frozen source SHA-256:

```text
24fb7ee970bc609f54a43cb7fa84e4a7f75bcbb7ac87381fd3fd79b8448c56a3  theories/self_interpreter/TelescopeBetaSignature.v
```

No timeout, admit, new axiom, unchecked cast or disabled check. Recursive
aggregate/kernel/pristine and full local CI evidence is separate, not
inferred from a module build.
