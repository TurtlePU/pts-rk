# Finite model internal realization — 2026-10-23

Owned source: `theories/CombinatoryLogic-rk/FiniteModelRealization.v` only.
No Dune, documentation, index, commit, or unrelated source edits.
Current final source is 477 lines, SHA-256:
`bf1868a7947fc1357f9a37cc7566c05d33b46d3d879cc1a60e19e2578aace91b`.

## Checked result and limitation

The output is literal `Syntax.Term nat n`, checked by original `Typing.typ`
with `Ranks.RankSorts`. Each semantic Boolean atom denotes independently fixed
Top or Void. A clause is the corresponding implication chain. Its executable
witness either returns Top or returns an existing false premise. Every valid
clause is realized without a semantic soundness/normalization assumption.

The certificate type is the finite continuation conjunction
`(C_1 -> ... -> C_k -> Void) -> Void`; it has exact rank at most 4, independently
of domain cardinality, schema count, valuation arity, and clause length.
Actual witnesses for false conjunctions would yield native Void through
explicit internal refuters; native canonicity proves the converse adequacy.

For each externally supplied candidate constructor algebra and complete finite
domain enumeration, an internal certificate exists iff the executable checker
accepts iff a genuine all-semantic-valuations predicate model exists. Every
individual selected positive/negative schema instance has an actual PTS witness
under every semantic vector. Both passing and second-valuation-failing Boolean
examples are checked.

This is an external all-index proof-producing family of INTERNAL finite model
satisfaction certificates. It is not an internal theorem with represented
fragment/budget arguments, no arbitrary Church-code coverage is claimed, and
it does not construct constructor algebras for every PTS fragment. The reverse
adequacy theorem uses external native Void canonicity; the forward witness
generator does not.

## Commands

Copied each version of the owned source into this unique temporary directory
before invoking the compiler. No generated object was written to the source
tree. Attempts 01–07 use the following command without the normalization `-Q`
line (their source did not yet import NativeCanonicity); attempts 08–11 include
it exactly as shown:

```sh
cp theories/CombinatoryLogic-rk/FiniteModelRealization.v \
  /tmp/pts-rk-finite-internal.6wfWep/FiniteModelRealization.v
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci \
  /Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- rocq compile \
  -Q /tmp/pts-rk-consistent-horn.2l5WGN/default/theories PTSrk \
  -Q /tmp/pts-rk-consistent-horn.2l5WGN/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-consistent-horn.2l5WGN/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -Q /tmp/pts-rk-finite-internal.6wfWep PTSrk.Combinatory \
  /tmp/pts-rk-finite-internal.6wfWep/FiniteModelRealization.v \
  > /tmp/pts-rk-finite-internal.6wfWep/attempt-NN.log 2>&1
```

The shell captured the compiler result and returned it after displaying the
log. Attempts 01–10 displayed only command output to the agent; exact tool exit
metadata was not separately archived. Their logs fully retain the failures
and successful assumption reports. Final attempt 11 explicitly observed tool
exit **0**, with **20 closed reports**, no warnings, no unsafe construct.

| Attempt | Observed result |
| --- | --- |
| 01 | Compiler error: an extra tactic after all goals were discharged. |
| 02 | Compiler error: imported lambda/list notation conflict. |
| 03 | Compiler error: missing `list bool` annotation on clause_rank. |
| 04 | Compiler error: missing Boolean annotation on realize_clause. |
| 05 | Compiler error: missing BoolClause list annotation on continuation_rank. |
| 06 | Compiler error: Nat.max equality oriented oppositely to lemma. |
| 07 | Eight closed reports; first clause/conjunction implementation. |
| 08 | Thirteen closed reports; internal refuters and checker linkage. |
| 09 | Compiler error: forallb_forall inference; replaced apply-in by rewrite. |
| 10 | Seventeen closed reports; exact certificate equivalence and regressions. |
| 11 | Exit 0, twenty closed reports; all-valuation instances and universal-model iff. |

The initial notation warning was fixed by excluding only Syntax's notation
import and using explicit `app`; no warning was suppressed.

Complete recursive checking, exit **0**, no `-admit`/`-norec`/skip flags:

```sh
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci \
  /Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-consistent-horn.2l5WGN/default/theories PTSrk \
  -Q /tmp/pts-rk-consistent-horn.2l5WGN/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-consistent-horn.2l5WGN/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -Q /tmp/pts-rk-finite-internal.6wfWep PTSrk.Combinatory \
  PTSrk.Combinatory.FiniteModelRealization \
  > /tmp/pts-rk-finite-internal.6wfWep/kernel.log 2>&1
```

Full context inventory contains inherited functional_extensionality_dep only;
no unsafe fixpoints, type-in-type, or assumed positivity. Dependencies are the
preceding fresh-audited directory, not rebuilt by this isolated check. Root is
responsible for the integrated fresh build and pristine comparison.

The final source/copy `cmp`, SHA-256 record, and
`git diff --no-index --check /dev/null theories/CombinatoryLogic-rk/FiniteModelRealization.v`
all pass, exit 0. Version command `rocq --version` recorded in version.log.

## MM0FiniteSignature.v

Additional owned source (394 lines), SHA-256:
`c56ad90c9957c5702063839850dbdb0e35592af504ddfe01289589e814e8e909`.
No previously frozen source was edited. Literal nine-constructor/eleven-
predicate/three-sort syntax; first-order sort checking is proved equivalent
to an independent SortedExpr formation judgment. Well-scoped interpretation
never consults its fallback value. Exact syntax-to-schema satisfaction and
complete semantic grounding range over all vectors. Pointwise-equal total
operation interpretations yield identical compiled clauses/checker results,
without functional extensionality. The interpretation gives each signature
sort its own copy of the same carrier D; unequal cardinalities are not covered.
This is a syntax transcription interface, not a parser-correctness claim.

All compiler attempts copied MM0FiniteSignature.v to this temporary directory
and used the same compile command as above, replacing the source basename and
log with `signature-NN.log`, and omitting the NormalizationComplexity -Q line.

| Attempt | Exit | Result |
| --- | --- | --- |
| 01 | 1 | Enumeration completeness needed tauto rather than depth-limited auto. |
| 02 | 1 | Patch-string backslash omission changed conjunction to division; repaired. |
| 03 | 1 | Schema reduction required explicit valuation instantiation. |
| 04 | 1 | Negative schema needed reduction before rewriting Forall_map. |
| 05 | 1 | Added explicit import of FiniteHorn for ConsistentModel. |
| 06 | 1 | Unavailable flat_map_map lemma replaced by direct list induction. |
| 07 | 0 | Twelve closed reports; initial complete semantic interface. |
| 08 | 1 | Vector.to_list length proof required existing Vector.length_to_list. |
| 09 | 0 | Final eighteen closed reports including independent sort/scope results. |

The upstream Vector advisory remains visible; no warnings were suppressed.
Complete recursive checking of PTSrk.Combinatory.MM0FiniteSignature with the
same maps (excluding NormalizationComplexity) passes exit 0, signature-kernel.log.
Its entire context inventory has NO axioms and no unsafe entries.

## FiniteModelSoundness.v

Additional owned source (176 lines), SHA-256:
`1f183a2441c9226ff37537480b4c24dd348a994fd0f9df41f14059dd199104a3`.
Independent source derivation trees in Type carry only actual selected-clause
membership and recursive premises. Inhabited Proof agrees exactly with the
existing GroundHorn derivability judgment. The executable mutual compiler
applies generated original-PTS clause proofs to compiled premise proofs.
Original typing is proved for ALL derivation depths. For saturation models
the model premise is discharged; selected denials compile to literal Void.
This is an all-index constructive external deduction translation, not an
internal theorem over arbitrary represented proof codes or fragment budgets.

Compile command is the original full command above with basename replaced by
FiniteModelSoundness and log soundness-NN.log. Dependencies include the frozen
FiniteModelRealization object in this temporary directory.

| Attempt | Exit | Result |
| --- | --- | --- |
| 01 | 1 | Generic induction tactic could not infer Horn relation parameters. |
| 02 | 1 | Unfolding the derivability alias alone did not resolve parameters. |
| 03 | 1 | Explicit mutual induction fixed that; denial target needed unfolding. |
| 04 | 0 | Fourteen closed reports; final deduction compiler. |

Source/copy comparisons and no-index whitespace checks for both additional
sources pass, exit 0. Final three-source hashes are final-sources.sha256.
The combined recursive check uses the full original maps and both roots
PTSrk.Combinatory.FiniteModelSoundness and PTSrk.Combinatory.MM0FiniteSignature;
its raw output is final-kernel.log. This check PASSES, exit 0; its complete
inventory contains only inherited functional_extensionality_dep, with no
type-in-type, unsafe fixpoint, or assumed positivity entries.

## MM0InternalSoundness.v — final integration

Additional owned source (178 lines), SHA-256:
`975d15cdb31b64b5e462d9709f1cbc807f37b4a2552b433c962caed02adb76b9`.
Twelve closed reports. The actual named MM0 selected-axiom schema now has an
explicit original-PTS finite satisfaction certificate whose inhabitance is
equivalent to a genuine all-valuations predicate model over the supplied total
constructor algebra. Successful exhaustive search supplies that certificate
for the returned algebra. Failure excludes such certificates only on that SAME
fixed domain. The explicit 53-rule projection interpretation has a CLOSED
certificate with no accepted-candidate/model/soundness premise and rank at
most 4. Acceptance is derived analytically from the explicit projection model;
no 2^28 exhaustive search or concrete saturation table is evaluated. The module
also integrates the original closed-AST proof compiler and specializes it to
the projection interpretation. Neither the omitted sveq/f0 axioms nor the
inactive Hilbert catalogue is silently restored.

After copying the source into this directory, compilation uses:

```sh
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci \
  /Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- rocq compile -time \
  -Q /tmp/pts-rk-consistent-horn.2l5WGN/default/theories PTSrk \
  -Q /tmp/pts-rk-consistent-horn.2l5WGN/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-consistent-horn.2l5WGN/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -Q /tmp/pts-rk-finite-algebra-search.LjN7h7 PTSrk.Combinatory \
  -Q /tmp/pts-rk-finite-operation-algebras.0JQW1q PTSrk.Combinatory \
  -Q /tmp/pts-rk-finite-internal.6wfWep PTSrk.Combinatory \
  -Q /tmp/pts-rk-native-model-boundary.iBL2hu PTSrk.Combinatory \
  -Q /tmp/pts-rk-mm0-finite-search.iwaQRP PTSrk.Combinatory \
  /tmp/pts-rk-finite-internal.6wfWep/MM0InternalSoundness.v \
  > /tmp/pts-rk-finite-internal.6wfWep/internal-03.log 2>&1
```

Attempts 01/02 used that same command without -time and their respective logs.

| Attempt | Exit | Result |
| --- | --- | --- |
| 01 | 1 | A change expression contained an uninferable Prop placeholder; supplied it explicitly. |
| 02 | 1 | Deliberately SIGINT-interrupted at concrete projection certificate: naive apply expanded its saturation. This is a failed/interrupted run, not a success. |
| 03 | 0 | Final twelve closed reports. Explicit theorem applications avoid concrete-table expansion. |

Final explicit projection certificate, rank and proof-translation specializations
each check in 0.000 seconds at the log precision. The generic certificate/source
bridge tactic applications take 23.858/21.377 seconds; no table is executed.
Source/copy comparison and no-index whitespace check pass exit 0. Exact hash is
also retained in internal-source.sha256. Sources frozen after this successful
compile; the parent is performing the 43-module fresh integrated audit, which
will provide the independent recursive check of this final integration.
