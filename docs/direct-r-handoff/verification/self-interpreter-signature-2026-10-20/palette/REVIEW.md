# Independent read-only review: equality operations and law families

Reviewed 2026-10-20 by the finite-palette agent, without editing either
reviewed module.

## IndexedCoherence

Source SHA-256:
`137c4fd12afe57ebea28692c5c456e510d5fd25254df6959f4acca6107f6973b`.
Read all definitions, typing derivations, reductions and assumption entries.
Contract review: PASS.

`compose_typed` composes actual homogeneous Leibniz witnesses at the same
predicate level. The two transports in its body have the correct shared
motive after original weakening. Its result equality type has the same
`max(a+2,b+1)` sort bound as the inputs. No symmetry is inferred.

`map_congruence_typed` is expressly NONDEPENDENT mapping: `g:A->B` lets
each predicate on B pull back along g, still at predicate level b.
Conversion only discharges the actual pullback beta applications. It does
not transport into a dependent family or equate functions from pointwise
evidence.

Reflexivity computation contracts to literal reflexivity syntax, including
the annotations. For arbitrary evidence, the identity laws are correctly
stated only after applying the evidence to its motive and input. There is
no eta contraction of `lambda P z.e P z` to e. Replacement lemmas are exact
original syntax equations. No source-conversion generator is assumed or
claimed.

Read the owner's `attempt-02.log`/`.exit` and `kernel.log`/`.exit` under
ignored `_build/indexed-coherence.BPcsC4`: compile exit 0, eleven closed
theorem reports; recursive check exit 0, only the existing upstream
functional-extensionality declaration in the loaded inventory, and no
unsafe fixpoints, type-in-type or assumed positivity. This review did not
rerun those checks or infer full-CI success from them.

## TarskiLawFamily

Read the initial six-endpoint module and the appended specialization
contracts while the owner was fixing their first compiler obligation.
Mathematical/API review: PASS. Subsequently inspected successful owner
attempt 10: exit 0 and eight closed reports, including both specialization
endpoints. Final reviewed SHA-256:
`9c302e23c9315eb14f12c14dda6fbf2267b88094f751a54820717d682d3fc423`.
This review did not rerun compilation or substitute for the aggregate audit.

`family_type` quantifies over arbitrary code A and genuinely dependent
code family B, hence one field suffices per external rank pair rather than
one field per type shape. For `c=max(a+1,b)`, its law body has sort c+2;
the surrounding domains have ranks 0 and a+1, so both original product
formations retain exactly c+2. No cumulativity is needed. Explicit carrier
and operation typings describe independently supplied local algebra data,
not a global interpretation result.

`identity_family` is a closed normal original term. Its original typing
first constructs reflexivity at the common plain dependent product and
then converts to the identity-specialized algebra interface via actual
reductions of the type. That law inhabitant is proved rather than assumed.
`family_specialize` applies the polymorphic field twice using original
typing; `identity_family_specializes` targets the literal already-constructed
identity-law term. No precomputed semantic normal form, eta principle, or
claim of full dependent quotation occurs.

## Palette cross-review

The separate equality-operation agent also reviewed the final
`TarskiPalette.v` read-only and reported PASS: actual bounded selectors,
original formation/normality, and independent `fill_typed` construction;
finite width `4(k+2)` for each external k and no conclusion-as-premise.
No source changes were requested.
