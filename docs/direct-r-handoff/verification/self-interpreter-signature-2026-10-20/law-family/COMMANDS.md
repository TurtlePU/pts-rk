# Polymorphic product-law family — 2026-10-20

Source: theories/self_interpreter/TarskiLawFamily.v.
SHA-256: 9c302e23c9315eb14f12c14dda6fbf2267b88094f751a54820717d682d3fc423.
Working directory: /Users/akuklev/air/pts-rk.
Fresh absolute build: /tmp/pts-rk-tarski-law-family.7qHIGy.
Raw local-only ignored evidence: _build/tarski-law-family.ggRr2a.

## Contract

For c=max(a+1,b), family_type is the ORIGINAL product
Pi A:Ca.Pi B:(Ea A->Cb).TC.product_law a b Ea Eb Ec p A B.
It has exact sort U_(c+2): the ranks of the two new binders are absorbed
because c>=a+1. Carrier/decoder/product typings are explicit local inputs,
not a premise assuming source quotation. One such field covers every
dependent A/B shape at the given rank pair.

The signature commutes literally with renaming/replacement, and is normal
when the six parameters are variables. family_specialize directly types
the two actual applications e A B at the local product-law type.

identity_family is the closed normal term lambda A:Ua.lambda B:A->Ub.
TI.identity_law a b A B. Its original typing is first constructed at a
plain reflexive product type, then converted to the actual identity-decoder
signature via proved common beta reduction. There is no subject expansion.
Two applications beta-reduce to the literal local identity law.
This constructs the polymorphic field required by the finite interface,
not arbitrary source-family congruence or full dependent quotation.

## Every build attempt

Each NN below used the following exact command:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-tarski-law-family.7qHIGy --display=short --no-buffer theories/self_interpreter/TarskiLawFamily.vo > _build/tarski-law-family.ggRr2a/attempt-NN.log 2>&1
law_status=$?
printf '%s\n' "$law_status" > _build/tarski-law-family.ggRr2a/attempt-NN.exit
tail -n 40 _build/tarski-law-family.ggRr2a/attempt-NN.log
exit "$law_status"
```

The displayed log-tail length varied (25--80); the build and saved complete
output did not. All exits were recorded immediately after Dune.

| Attempt | Exit | First result |
| --- | --- | --- |
| 01 | 1 | family_type_replace: incomplete nested substitution simplification. |
| 02 | 1 | Diagnostic Show exposed nested lifted renamings in the same goal. |
| 03 | 1 | Modular replacement lemmas fixed that goal; arr_shift rewrite did not match an implicit shifted universe. |
| 04 | 1 | Explicit weakening fixed it; cbn obscured max in the numerical sort equation. |
| 05 | 1 | Explicit numerical equation fixed it; final family-variable lookup needed code_family_shift. |
| 06 | 0 | Signature sort/replacement proofs compiled, one own closed report. |
| 07 | 0 | Normal closed identity family and exact signature conversion compiled, six own closed reports. |
| 08 | 1 | New family_specialize: first substitution equality retained lifted successor replacements. |
| 09 | 1 | Diagnostic Show exposed that same equality. |
| 10 | 0 | Explicit transpose/fin_match and existing replace_fsucc close it; complete module, eight own closed reports. |

No timeout occurred; all temporary Show commands were removed. No theorem
was weakened, no axiom/admission/check bypass introduced. Known loadpath
remapping warnings remain. Independent mathematical/API reviews pass.
The final integrated fresh build, recursive checks, source stability and
full CI are recorded separately in the checkpoint's final-review report.

Own assumption endpoints: family_type_sort, family_type_normal,
family_type_replace, family_specialize, identity_type_recovers,
identity_family_typed, identity_family_normal, identity_family_specializes.
All eight print Closed under the global context in attempt 10.
