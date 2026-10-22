# Total application regressions

From `/Users/akuklev/air/pts-rk`, both checks used:

```sh
/tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries \
  -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
  -i theories/CombinatoryLogic-rk/agda \
  theories/CombinatoryLogic-rk/agda/ApplicationExamples.agda
```

Outputs were redirected to attempt-01.log and attempt-02.log, respectively.
Both exit 0 without warnings. The first verifies dependent polymorphic
identity application and genuine conversion-rule inputs. The second adds a
rank-bounded annotation-redex example using NativeDescent and original
subject reduction, retaining its unreduced dependent product type.
No failure, timeout, postulate, hole or unsafe option occurred.

The initial inspection also attempted to read NativeNormalization.agda,
which does not exist (read command exit 1); the actual normalization theorem
is in NativeDescent.agda. This was not a compiler failure.

Final hash:

```text
4ef2df4ee80d378e9228f8b14eec037c9ef5824f494b44d4c8d463cdf15aa47a  ApplicationExamples.agda
```

Scoped git diff whitespace check exits 0. Root integrates Everything and
performs the separate fresh complete import-closure check.
