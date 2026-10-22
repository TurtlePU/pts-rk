# Concise self-interpreter note — 2026-10-22

Only the note source and its generated PDF were edited in this documentation
pass. No proof sources were changed after the parent froze its manifests.

The replacement is 661 source lines / 28 KB / 10 PDF pages, versus 1044 source
lines / 45.6 KB / 15 PDF pages. It leads with typed telescope algebras and actual
type/term folds, then distinguishes tag-free recovery from unresolved full
intrinsic fidelity, common API from rank-only signature, and fixed execution
head from internal accepted-proof reification.

Build commands (working directory: /Users/akuklev/air/pts-rk):

```
bash tools/build-self-interpreter-note.sh > _build/phoas-fold-design/note-01.log 2>&1
bash tools/build-self-interpreter-note.sh > _build/phoas-fold-design/note-02.log 2>&1
bash tools/build-self-interpreter-note.sh > _build/phoas-fold-design/note-03.log 2>&1
git diff --check -- PTS-rk_self_interpreter.tex
```

All three builds exited 0. Build 1 (/tmp/pts-rk-self-note.yWPcx2) nevertheless
rendered one math block as text because a trailing backslash was parsed as a
Markdown line break; the 9.54pt overfull warning and PDF text inspection exposed
this. Replacing it with an inference fraction fixed the rendering. Build 2
(/tmp/pts-rk-self-note.ddsBCM) had no overfull/reference/glyph issues and one
harmless final-paragraph underfull warning. Build 3
(/tmp/pts-rk-self-note.tiwZMq) is the final compiled version; a concise closing
paragraph removes that warning too.

Final log scan:

```
rg -n 'Overfull|Underfull|LaTeX Warning|Missing character|markdownRendererDollarSign' \
  /tmp/pts-rk-self-note.tiwZMq/PTS-rk_self_interpreter.log \
  /tmp/pts-rk-self-note.tiwZMq/_markdown_PTS-rk_self_interpreter
```

Exit 1, no matches. Diff whitespace check exit 0. PDFKit text inspection reports
10 nonempty pages, no literal backslash or double-dollar math leakage. It is not
a substitute for the parent's final visual PDF review.

Primary-source comparison rechecked directly with PDFKit in the supplied
2914770.2837623.pdf, document pages 8–10 (printed pages 12–14): nf is a normal-form
checker, not a normalizer; semantic correctness is proved for unquote/isAbs/size/nf,
not CPS. Displayed CPS is call-by-name and answer-polymorphic; CBV is mentioned.
Agent intrinsic_fidelity read the complete final note and found the mathematical
contracts accurate. A proposed extra generic first-class fold head is NOT claimed
here before it is implemented/checked; this version explicitly specializes a
chosen signature and filling.

SHA256:

```
5a8c294cb24b4ca3f4db4220f37856412e33c919e1c2259e34a31a5c53fe9761  PTS-rk_self_interpreter.tex
3a9424d4c666d115402bf03f1648fc47c095421996bd48764c3ca3e6740e2049  PTS-rk_self_interpreter.pdf
```

## Generic ordinary-argument head integration (supersedes final hashes above)

Independently reviewed the complete checked temporary module
/tmp/pts-rk-generic-fold.AlVdu8/GenericFold.v. Its head contains the finite
signature and decoding families but no algebra filling. Its run is the literal
ordinary application spine head P Q alpha_1 ... alpha_m. Specializing P,Q alone
returns lambda Sigma.Q Sigma, not an eta-reduction to Q. Head normality requires
normal declarations/C/E and neutral E; it does not require normal argument
fields. The proved type-sort simplifies arithmetically to
max(rank rs 0 + 1, rank rs s + 1). Composition is an untyped syntactic beta
theorem for nested folds, not a semantic fusion theorem or an assertion of
cross-signature typing compatibility. No proof source was edited in this pass.

Added a concise generic-head paragraph and its equation/rank to the note, plus
an introductory module entry. No rank-only/common-signature theorem is claimed.

```
bash tools/build-self-interpreter-note.sh > _build/phoas-fold-design/note-04.log 2>&1
bash tools/build-self-interpreter-note.sh > _build/phoas-fold-design/note-05.log 2>&1
git diff --check -- PTS-rk_self_interpreter.tex
```

Both builds exit 0. Build 4 is /tmp/pts-rk-self-note.VqoeSX, build 5 is
/tmp/pts-rk-self-note.jV3hSY. Build 5 merely splits the displayed head and beta
equation into two aligned lines. Both logs have no overfull/underfull/LaTeX
warnings, missing glyphs, or Markdown-rendered dollar delimiters.
Final PDFKit check: 10 nonempty pages, no literal TeX leakage, exit 0.
Final whitespace check: exit 0. Current source length: 682 lines.

```
ed8f8889da1899edb59de56d78c544c7ce20d672e2924abb85188a25674404a4  PTS-rk_self_interpreter.tex
8449df3a096ac16010ed2c163903bcb8a5ba8849090fa58dcda04edfa469688c  PTS-rk_self_interpreter.pdf
```

## Final fidelity wording review (supersedes final hashes above)

Changed the description shared by the simply typed and binder-free codes from
an intrinsic structural decoder to intrinsic structural syntax-injectivity
proofs. The former could incorrectly suggest an executable arbitrary-PTS-to-tree
parser. No proof contracts or sources changed.

```
bash tools/build-self-interpreter-note.sh > _build/phoas-fold-design/note-06.log 2>&1
git diff --check -- PTS-rk_self_interpreter.tex
rg -n 'Overfull|Underfull|LaTeX Warning|Missing character|markdownRendererDollarSign' \
  /tmp/pts-rk-self-note.a3CRxJ/PTS-rk_self_interpreter.log \
  /tmp/pts-rk-self-note.a3CRxJ/_markdown_PTS-rk_self_interpreter
```

Build 6 exit 0, whitespace check exit 0, log scan exit 1 with no matches.
Final PDFKit text check exit 0: 10 nonempty pages, no raw TeX leakage.
Full raw build: /tmp/pts-rk-self-note.a3CRxJ/build.log.
Source length remains 682 lines.

```
78e281fc4eaaacc27b89023af068abec7587e7c48988f5a67790ca1694c2fe55  PTS-rk_self_interpreter.tex
38969cc6981ea508a6bef9c8cd4e71aa65f3b69e0f5de11de53b3736d773370c  PTS-rk_self_interpreter.pdf
```
