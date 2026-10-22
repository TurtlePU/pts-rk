# FragmentPackages incremental verification

Working directory: /Users/akuklev/air/pts-rk.
Only new theories/CombinatoryLogic-rk/agda/FragmentPackages.agda was edited.
Existing sources, Everything, documentation, Git index and commits were not changed.

Compiler: Agda 2.8.0-3d04bac.
Cubical: b150186d2544e7efeddd31e5d14a8b9ecbb100f7.

Every compiler attempt used:

```sh
/tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries \
  -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
  -i theories/CombinatoryLogic-rk/agda \
  theories/CombinatoryLogic-rk/agda/FragmentPackages.agda > LOG 2>&1
```

| Log | Exit | Outcome |
| --- | --- | --- |
| attempt-01.log | 0 | Joint context/element and normal-morphism finite carriers, no warnings |
| attempt-02.log | 42 | Implicit middle grades under nested maximum not inferable |
| attempt-03.log | 0 | Explicit numeric grades; arbitrary raw valuation coverage, no warnings |
| attempt-04.log | 0 | Automatic valuation coverage source/target/images recovery, no warnings |

ContextElementPackage counts context codes, normal type codes and normal
term codes simultaneously. Its well-formedness, original typing and type-rank
evidence are truncated; finiteness does not quantify over an external infinite
context index. contextMaxNodes and encode-context-code give exact bounded
encoding of every actual native context. package-in-context transfers an
actual finite typed element into the joint carrier with exact recovery.

MorphismPackage counts both endpoints and normal valuation images.
RawMorphismPackage separately counts arbitrary bounded raw images; it does
not assume simultaneous normalization of dependent tuples. Both have explicit
injective finite bounds and native substitution soundness. cover-valuation
computes alphabet and node bounds for every original valuation between
well-formed contexts and proves exact source/target/image recovery.

These packages are finite at each fixed scope/alphabet/size/rank grade. They
do not assert that a single grade is closed under unbounded operations.
No postulates, unsafe pragmas, holes or disabled checks were added. These
are incremental checks; the root performs the fresh complete safe closure.
