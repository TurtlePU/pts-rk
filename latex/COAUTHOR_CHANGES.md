# Coauthor changes synchronized from upstream

Compared the last two commits on TurtlePU/pts-rk main:

- [a3fbee5 — Oxford English + better authors](https://github.com/TurtlePU/pts-rk/commit/a3fbee5ba189496c6402f22dd1563615f89bb524)
- [f06c6f2 — choose different exponent for fun](https://github.com/TurtlePU/pts-rk/commit/f06c6f27ab095aa7036d2112124bd344add49d2a)

The comparison baseline is their parent, `535d9b4`. The local baseline is
`449bb43`. Changes below were absent from that Markdown paper and are now
applied. Existing Oxford spelling, comma/article corrections, metadata,
and the shortened closedness paragraph are not repeated here.

## Changes beyond the wording suggestions

1. **Abstract:** “without any additional axioms” → “without additional axioms”.
2. **Introduction:** rewrites the opening into two sentences, explicitly names
   Berardi and Terlouw, restores the variable clause `$x ∈ \mathsf{Var}$`,
   uses “dependent function types” with the parenthetical dependency clause,
   and changes “act as” to “act like” (subsequently restored to “act as”
   by the local author, who also added “(PTS)”). The sentence split implements
   G-L43, which was already checked in the old report.
3. **Normalization overview:** replaces the local “All lambda cube PTSs …
   but it is not hold in general” paragraph with “Both STLC and CoC are
   strongly normalizing … but it is not true for arbitrary PTS.”
4. **Motivating questions:** “took interest” → “took an interest”. This does
   not implement D04-L204’s proposed “Upon observing … became interested”.
5. **Internal references:** renames `formalisation` and `normalisation`
   labels and all their references to `formalization` and `normalization`.
6. **Complexity overview:** explicitly includes type checking alongside
   convertibility in the opening TOWER-completeness statement.
7. **Representation bound:** replaces the incorrect logarithm by an outer
   exponential and retains the outer base `e` in both expressions:
   `$\mathcal{O}(e ↑ (c ↑ … ↑ c ↑ i(n_1, …, n_k)))
   = \mathcal{O}(e ↑ c ↑ … ↑ c ↑ i(n_1, …, n_k))$`.
   The first commit changes `log` to exponentiation; the second changes
   the outer base to `e` and makes it explicit on the right as well.
8. **Finite separation:** “Specialising” → “Specializing”. The adjoining
   “to these data” → “with these data” implements D42-L2421.

## Wording suggestion status

WORDING_SUGGESTIONS.md now has **44 checked entries** and **13 unchecked
entries**. Of the checked entries, 43 are newly checked; G-L43 was already
checked and its requested sentence split is now actually present.
The original proposals and provider attribution are retained, and their line
ranges point to the corresponding passages in the updated Markdown source.

The following checked entries use the coauthor’s wording rather than the
literal suggested replacement:

- D09-L467: “slightly differs”, rather than “differs slightly”.
- L511-S1-P1: the rewritten inversion-lemma paragraph uses “there is a
  family … They are …”, resolving agreement without replacing “are” by “is”.
- L705-S1-P1: “cases are”, rather than “case is”.
- D24-L1260: “the non-formal treatment given above”, rather than “written above”.
- D37-L2066: “as” and “because”, rather than “as” and “for”.
- D39-L2181: “We now begin”, rather than “We will begin by”.
- D41-L2320: “This proposition asserts that a negation of P is upwards
  closed for ‘good’ values in the new domain X”, rather than “This means that …”.

Two unchecked entries are **partly implemented**:

- L1556-S2-P1: “there are” is implemented; “on terms” remains, rather than
  the suggested “in terms”.
- D40-L2229: “To lift … to” is implemented; “let” is retained.

## Preserved differences

- Upstream introduces the typo “enoug”; the Markdown paper retains “enough”.
- Upstream switches the traditional paper to T1 font encoding and `authblk`,
  with author lines, ORCID links, email links and numbered affiliations.
  The Markdown class already provides that author layout and its LuaLaTeX
  font configuration, so these traditional-TeX implementation details are
  not copied into the Markdown source.
- Earlier intentional local choices remain: the smaller unindented abstract,
  its “normalizing” wording, omission of the article before the Π-former,
  explicit date and page breaks, the removed introductory Gödel 1940 citation,
  the rank-bound code figure and its introduction, concise formalization badges,
  and the corrected `d X s z` argument order. These are not changes introduced
  by the two upstream commits.

The traditional local paper.tex is not changed by this synchronization.
