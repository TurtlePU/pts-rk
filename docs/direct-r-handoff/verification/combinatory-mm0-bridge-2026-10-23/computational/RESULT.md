# Literal computational source adequacy

MM0ComputationalAdequacy.v is compiled and recursively kernel-checked.
The final compilation, attempt-22, exits 0 at 19:14:23–19:14:28 UTC on
2026-10-23 and prints 37 closed assumption reports. The complete recursive
kernel check exits 0 at 19:14:50–19:15:02. Its whole context inventory matches
the previous freshly compiled pristine upstream inventory after whitespace
normalization: inherited functional_extensionality_dep only, no unsafe items.
No dependency skip/admission flags were used.

Exact commands, exit codes and start/end timestamps are retained per attempt.
The wrappers use the pinned pts-rk-ci opam environment and the previously
fresh guarded-fragment dependency directory. The new source is copied to
/tmp/pts-rk-mm0-computational.3tS6OZ; successful source/compiled-copy equality
and SHA256 are checked by FINAL.sh. This is not a new full repository build.

The original MM0SyntaxSoundness.Derivation is the source judgment throughout.
Induction proves all nine computational predicates sound for every source
axiom selection. The converses construct source derivations using the full
55-axiom list. Numeric ordering/max, binder-aware lift/substitution, raw beta
reduction, ranked telescope prefixes, forms and the substitution telescope
all have exact iff interfaces on correctly sorted ground inputs. Prefix
length and form exposure bounds are derived, not assumed. PAx and PH remain
uninterpreted in this computational invariant and are handled by the separate
catalogue/native modules.

Attempts 01, 11, 13, 18, 21 and 22 pass; the other attempts exit 1 at the first
proof elaboration error. Their logs remain, including alias unfolding,
boolean rewrite, explicit numerical instantiation and sorting-tactic repairs.
No failed run is relabelled successful.

Commands:

```sh
bash docs/direct-r-handoff/verification/combinatory-mm0-bridge-2026-10-23/computational/CHECK.sh attempt-22
bash docs/direct-r-handoff/verification/combinatory-mm0-bridge-2026-10-23/computational/KERNEL.sh
bash docs/direct-r-handoff/verification/combinatory-mm0-bridge-2026-10-23/computational/FINAL.sh
```

Final source SHA256:
8754f576fb266a979d2b4c54ee4ece362a1d7841b7b1d88224f6e3d30a821c39.
Only the owned source and evidence files were edited; no staging or commits.
