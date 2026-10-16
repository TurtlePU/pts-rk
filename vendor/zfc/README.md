# Pinned ZFC subset

Source: https://github.com/rocq-archive/zfc
Commit: `ede7126560844c381c2b021003a8dbcb0668ecad`.
Author: Benjamin Werner. License: LGPL-2.1-or-later; see LICENSE and file headers.

Only Sets.v, Axioms.v and Cartesian.v are currently needed. Their Ens, EQ, IN,
separation, powerset and ordered-pair constructions are used directly, not
replaced by a new axiomatization. The upstream monolithic zfc.v is not imported.

Compatibility change: Cartesian.v's removed `elimtype F` tactic is replaced
with `enough (Hempty : F) by destruct Hempty`. No statements or axioms change.
Final empty lines are normalized. Dune configuration is local.

The full upstream Makefile was tried under Rocq 9.2 and failed at the removed
`elimtype` tactic in zfc.v. The modular subset is built by this repository.
The library does not supply the finite-aleph/GCH cardinal-arithmetic machinery
needed to finish the paper's model. This subset does not assume choice, GCH,
or PTS soundness.
