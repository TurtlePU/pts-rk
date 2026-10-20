# Original dependent-context normalization — 2026-10-20

`CanonicalContexts.v` defines the executable metalevel transformation

```text
normalize_context empty = empty
normalize_context (G & A) = normalize_context G & OpenCanonical.nf G A.
```

Each declaration is normalized under its original prefix. The main
`normalize_context_structure` proof inducts on the original Type-valued
well-formedness witness, retaining its actual formation ranks, and constructs
original well-formedness plus identity `TypedSub` in BOTH directions.
Declaration conversion is justified by original beta reduction and
`typ_conv`, not by an assumed transport law. No Prop rank witness is eliminated
into Type, and no typing rule or source domain is changed.

`normalize_typing_iff` transports the literal original term and supplied type
unchanged in both directions, including all lambda annotations. Other
endpoints prove declaration normality, idempotence, reduction by the original
`ctx_beta` relation, reduction of actual context lookup types, and agreement
of normal forms computed under original and normalized contexts. This is
metalevel dependent-context transport, not an object-language universe decoder
or a complete dependent PHOAS interpreter.

Only the new source, this report, and its one module token in the existing
SelfInterpreter Dune declaration were edited by this module owner. Other
parallel source additions were preserved. No Git mutation was performed.

Exact compiler command from the repository root:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH \
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam \
opam exec --switch=pts-rk-ci -- dune build \
  --build-dir=/tmp/pts-rk-canonical-contexts.Q4XTun --display=short --no-buffer \
  theories/self_interpreter/CanonicalContexts.vo \
  > _build/canonical-contexts.kmrd9j/attempt-NN.log 2>&1
build_status=$?
printf '%s\n' "$build_status" > _build/canonical-contexts.kmrd9j/attempt-NN.exit
tail -40 _build/canonical-contexts.kmrd9j/attempt-NN.log
exit "$build_status"
```

The absolute Dune directory was freshly allocated for this module. Raw logs
and exact exit files remain in ignored `_build/canonical-contexts.kmrd9j`.
Attempt 01 exited 1 because weakening required the shifted variable/type
forms to be made explicit. Attempt 02 exited 1 on an automatically generated
well-formedness-induction hypothesis name; explicit induction names fixed it.
Attempt 03 exited 1 on an uninferred intermediate context in a reflexive-
transitive closure proof; supplying that actual intermediate context fixed
it. Attempt 04 exited 0 with ten `Closed under the global context` reports.
No timeout or disabled check occurred. Existing overlapping-loadpath warnings
remain visible. Independent read-only contract review passed with no fixes.

Toolchain inventory (exit 0):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH \
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam \
opam exec --switch=pts-rk-ci -- sh -c \
  'rocq -v; dune --version; ocamlc -version; opam list --installed --columns=name,version' \
  > _build/canonical-contexts.kmrd9j/versions.log 2>&1
```

Observed pins: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1. Scoped `git diff --check` exited 0.
Root owns final aggregate fresh assumptions, recursive kernel checking and
full CI; this report asserts only the local module build and read-only review.

Frozen source SHA-256:

```text
0f3e33864857fe81c2eb114b0c08022ca3ffb11ec3439db91676a95546e3b858  theories/self_interpreter/CanonicalContexts.v
```
