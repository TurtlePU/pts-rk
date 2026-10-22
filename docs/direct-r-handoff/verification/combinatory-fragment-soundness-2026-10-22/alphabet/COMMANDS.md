# FragmentAlphabet incremental verification

Working directory: /Users/akuklev/air/pts-rk.
Only new theories/CombinatoryLogic-rk/agda/FragmentAlphabet.agda was edited.
Existing sources, Everything, documentation, Git index and commits were not changed.

Compiler: Agda 2.8.0-3d04bac.
Cubical: b150186d2544e7efeddd31e5d14a8b9ecbb100f7.

Every attempt used:

```sh
/tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries \
  -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
  -i theories/CombinatoryLogic-rk/agda \
  theories/CombinatoryLogic-rk/agda/FragmentAlphabet.agda > LOG 2>&1
```

| Log | Exit | Scope |
| --- | --- | --- |
| attempt-01.log | 0 | Generic structural injection; normal/fragment alphabet functor laws |
| attempt-02.log | 0 | Concrete coherent Fin inclusions; raw application naturality |
| attempt-03.log | 0 | Native erasure injectivity for injective dictionaries; conversion reflection |

All three runs complete without warnings. These are incremental checks;
the parent will run the fresh complete safe closure. No postulates, unsafe
pragmas, holes, assumptions of normalization or disabled checks were added.

Dictionary agreement is pointwise equality of decoded universe labels.
Injectivity is needed only to reflect finite code equality, not to preserve
native meaning. Empty alphabets are covered without a retraction premise.
Application naturality retains each existing executor's alphabet capacity
premise; it does not assert a bound on host allocations or a closed fixed
carrier under arbitrary applications.
