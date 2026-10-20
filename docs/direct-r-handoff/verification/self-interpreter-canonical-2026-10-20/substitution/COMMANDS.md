# Full-PTS hereditary substitution — 2026-10-20

Source: theories/self_interpreter/CanonicalSubstitution.v.
SHA-256: 1a3e89fb34d28c816e5a95b423d252d373a3ad2ae7e51c68226a67445acf6ed4.
Raw local compiler output: _build/canonical-substitution.mrS2aY.
Absolute incremental Dune directory: /tmp/pts-rk-canonical-substitution.Pat3kK.

The four numbered compiler attempts target CanonicalSubstitution.vo in that
directory, using the pinned environment. Reproduction command from the root:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH \
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam \
opam exec --switch=pts-rk-ci -- dune build \
  --build-dir=/tmp/pts-rk-canonical-substitution.Pat3kK \
  --display=short --no-buffer theories/self_interpreter/CanonicalSubstitution.vo
```

Attempt 01 exited 1: bare var still had explicit sort/scope parameters in
typed_sub_identity; use the actual substitution lambda i => var i. A separate
dependency build also exposed the missing explicit Greedy import for normalb;
its complete failure is recorded as attempt 04 in the type-index report.
Attempt 02 exited 1: the composition proof's change command could not infer
the right-hand-side placeholder. Repeating the actual right-hand side fixed
the proof command. Attempt 03 exited 0, with seven closed assumption reports.
Attempt 04 added hsubst_canonical_typed and exited 0 with eight closed reports.
No statement was weakened, no assumption added and no timeout occurred.

The new public results use actual original TypedSub and Typing.typ:

- Normalized substitution entries retain their dependent lookup typings.
- Hereditary substitution normalizes after literal replacement, preserves
  typing, and also types the result at the normalized substituted type.
- Normalizing the source and substitution entries before hereditary
  substitution does not change the resulting literal normal form.
- Identity returns the source normal form; composition normalizes the
  composite entries and equals successive hereditary substitutions.
- Source beta conversion implies equality of hereditary results.

Original validity supplies exact source-type sorts; original preservation,
conversion and normal-form uniqueness discharge the coherence obligations.
No cumulativity, eta rule or target-as-premise is used. These are executable
metalevel original-syntax operations, not an internal PHOAS interpreter.

The final fresh combined audit (not this incremental target's cache) verifies
all eight reports and recursive kernel dependencies. Exact commands, pinned
versions, pristine comparison and all 226 CI stages are in
[the final review](../final-review/COMMANDS.md). Independent API review passes.
