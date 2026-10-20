# Shared-map conversion obstruction — 2026-10-20

`PHOASConversion.v` proves a deliberately limited no-go theorem, not an
impossibility of dependent PHOAS. The original closed type terms
`((lambda X:U_0. X) U_0)` and `U_0` are distinct but beta-convertible, both
originally typed at `U_0`. Both satisfy the independently defined `SmallType`
domain: type rank zero, largest literal zero, at most five nodes, and common
sufficient redex bound six (the latter is conservative, not claimed minimal).

`no_shared_map_on_types` excludes simultaneous quotation normality, literal
source injectivity and preservation of source beta conversion on any domain
admitting those witnesses. `no_fixed_index_shared_map` makes the boundary
explicit for an arbitrary external family index: increasing budgets does not
repair the three incompatible contracts at a fixed member admitting both.
`no_faithful_code_agrees_with_index` also excludes a faithful normal code map
pointwise beta-equivalent to a separate conversion-preserving index map.
It does **not** exclude genuinely separate syntax codes and semantic or
canonical type indices; ordinary dependent PHOAS need not impose agreement
between these two roles. No target typing premise is needed for the no-go.

No core/source-domain rules, axioms, admitted proofs, unsafe operations or
disabled checks were introduced. No full-dependent-interpreter impossibility
claim is made. Root owns Dune/Audit integration and the final aggregate audit.

Pinned environment and exact command:

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
opam exec -- dune build --build-dir /tmp/pts-rk-phoas-conversion.jNIaKA theories/self_interpreter/PHOASConversion.vo
```

Literal launcher and all outputs are retained in ignored
`_build/phoas-conversion.KyvwMG`: `RUN.sh`, `attempt-01.log` through
`attempt-04.log`. The first build directory was fresh. Attempt 01 exited 1
because `nodes` required an explicit `Bounds` import; attempt 02 exited 0.
After adding the two-map endpoint, attempt 03 exited 1 because implicit domain
inference selected `Type` rather than `Prop`; the explicit intended `Prop`
annotation fixes that. Final attempt 04 exited 0 and printed seven
`Closed under the global context` reports. These are real compiler results;
no recursive kernel/pristine or full-CI result is claimed by this module-only
check. Existing overlapping-loadpath warnings remain visible in the logs.

Final source SHA-256:

```text
29c3452e4817e387b4f2e82ef50309e4720fb7068d9382cbcb589bc7f787e8c6  theories/self_interpreter/PHOASConversion.v
```
