---
name: prose-review
description: Collect Grazie and DeepL Write wording suggestions for LaTeX–Markdown prose, protecting mathematics and technical terminology and producing source-aligned CriticMarkup for coauthor review.
---

Use this add-on for a review report, not automatic editing of the document.
Read [the service workflow](references/services.md) before cloud collection.

`scripts/review.py prepare SOURCE --output MANIFEST.json` extracts prose,
unwraps sentences and masks formulas, references, code and unknown macros.
It retains source offsets and line flow. Inspect the manifest before sending
it externally; an unknown macro is not a license to expose its contents.

Use the user's actual requested services. Prefer an existing signed-in
Grazie UI/IDE or a supported authenticated adapter. Do not extract passwords,
cookies or bearer tokens from private stores, invent endpoints or describe
local flat-tree rules as Grazie cloud. Stop on login challenges, quotas or
service limits; request an authenticated session/export when necessary.
An unavailable service does not prevent preparing/filtering the other report.

For DeepL, use `scripts/deepl.cjs` with a dedicated, explicitly exposed CDP
browser tab. It requires Node and `ws`; it never starts a browser, chooses a
profile or reads cookies. Paragraphs are sent without internal line breaks.
For Grazie/cloud adapters, `review.py collect` uses the same manifest and
explicit JSON protocol documented in the service workflow. Keep exact
provider/engine evidence, raw inputs and outputs out of the concise report.
For persistent browser authentication, `grazie-session.cjs init|start` launches
only a dedicated private profile outside repositories. The user installs the
official extension and signs in once; the browser retains credentials. This
is session setup. `grazie.cjs MANIFEST.json RAW.json` drives the signed-in
official extension's empty Text Playground and observes only its actual cloud
proofreading responses; `grazie-normalize.py MANIFEST.json RAW.json RESULTS.json`
converts verified sentence-relative UTF-16 fixes for the report renderer.
Read the service workflow before using it; never expose the debugging port
beyond loopback.

`review.py render --source SOURCE --results RESULTS.json --output REVIEW.md`
filters suggestions and emits one CriticMarkup passage per affected prose
block. `--terms FILE` adds project-specific protected words/phrases, one per
line. Defaults protect sort/type/term/rank and other mathematical concepts.
`--names FILE` protects people, surnames, institutions and named systems,
including possessive uses, independently of the technical glossary.
`--exclude FILE` supplies additional unwanted replacement words. Check the
filter audit, especially rejected blocks, before claiming complete coverage.
Do not edit merely to evade a filter. Ambiguous matches fail closed.
`review.py merge RESULTS... --output COMBINED.json` combines provider evidence
for the same source hash. Rendering collapses identical restored CriticMarkup
at the same source span and lists both providers once. Different or partially
overlapping rewrites remain separate alternatives, not invented hybrids.
Independent non-overlapping edits with the same provider attribution and
source span share one passage; conflicting edits are never combined.

Keep source mathematics, reference keys, code, macro arguments, Oxford
spelling and technical meanings unchanged. Drop spelling-only variant edits,
known false positives, altered/missing placeholder results and terminology
rewrites. Do not clutter the report with excluded examples or repeated hints.
Use `{~~old~>new~~}`, `{++addition++}`, `{--deletion--}` and `{>>comment<<}`;
never put one CriticMarkup edit across paragraphs or code/math spans. Keep
unchanged source line breaks rather than flattening or rewrapping the report.
Rejecting the markup must reproduce the exact source excerpt.

For GitHub review, wrap each CriticMarkup token in single backticks. Put the
checkbox immediately before its source-aligned passage, without a separate
“Review” or “Implemented” line. Use headings in this order:
`paper-markdown.tex:214-218 · EDIT-ID · Suggested by Grazie & DeepL Write`.
Display both cloud and IDE engines simply as Grazie; retain precise engine
and coverage evidence in the audit, not repeated report status lines. List
both providers when the same edit is independently supported; do not infer
shared support for merely similar or conflicting alternatives.

Review retained edits for connected rewrites whose partial rejection would
leave ungrammatical prose. Protect additional project terms as needed. Show
only genuine service suggestions, mark unavailable services honestly, and
never imply an unflagged edit is mathematically certified. Do not apply,
commit, push or install an extension without the corresponding request.

Before publishing a report, perform a mandatory name/terminology audit:
inventory proper names from prose, author metadata and cited authors, and
technical words/phrases from definitions. Supply these as `--names` and
`--terms` to the common renderer for BOTH providers. Inspect every retained
replacement for unknown names or mathematical vocabulary missed by the lists;
extend the lists and rerender from immutable results. Do not trust a service's
spelling classification, substitute a different surname, or silently correct
technical hyphenation/capitalization. Keep punctuation-only edits around an
unchanged name reviewable. If a connected rewrite changes a name or technical
concept, drop that whole proposal rather than salvaging a potentially broken
fragment. Keep excluded examples out of the concise report, in its audit only.

Run tests with `python3 -m unittest discover -s tests` from this add-on.
With `ws` available, `node tests/test_deepl.cjs` exercises the CDP adapter
against a local fixture, including existing-draft protection; it contacts
neither DeepL nor Grazie.
