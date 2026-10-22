# FragmentModelExamples incremental verification

Working directory: /Users/akuklev/air/pts-rk.
Only new theories/CombinatoryLogic-rk/agda/FragmentModelExamples.agda was edited.
Existing sources, Everything, documentation, Git index and commits were not changed.

Compiler: Agda 2.8.0-3d04bac.
Cubical: b150186d2544e7efeddd31e5d14a8b9ecbb100f7.

Both compiler attempts used:

```sh
/tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries \
  -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
  -i theories/CombinatoryLogic-rk/agda \
  theories/CombinatoryLogic-rk/agda/FragmentModelExamples.agda > LOG 2>&1
```

| Log | Exit | Outcome |
| --- | --- | --- |
| attempt-01.log | 0 | Closed identity, dependent substitution and malformed derivation regressions |
| attempt-02.log | 0 | Nonempty target-context package and malformed valuation rejection |

Both runs complete without warnings. Raw ModelInput values contain only
independent context, valuation and typing-certificate data. Successful
checking is by computation; output typing is derived through the generic
model soundness theorem. Normal-form uniqueness identifies the identity
value and exact type. A nonempty valuation instantiates X:U0 by U0 in
lambda x:X.x. Another interprets X by Y in a nonempty target context and
checks that the finite joint package decodes that actual context.

Incorrect variable typing and a valuation proof tree that does not match
its declared image both compute rejection before normalization. No native
typing conclusion, normalization hypothesis, postulate, unsafe pragma,
hole or disabled check occurs as an input field.

These are regressions for the generic theorems, not a substitute for their
all-input proofs. They do not establish a fixed finite first-order model.
The root performs the fresh complete safe closure.
