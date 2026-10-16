# Service workflow and evidence

## Authentication

Use an already authenticated browser/IDE or a user-provided supported adapter.
Never ask the user to paste a password or put credentials in a manifest,
report, command argument or repository. If an IDE's inspection CLI refuses
because the IDE is running, ask the user to close it or export findings;
do not terminate it or copy its credential store. A CLI/IDE inspection is not
proof of cloud execution: retain engine/connection evidence from that run.
Paid usage, extension installation and changing global IDE settings need
appropriate user authorization. Do not switch to another service silently.

### Reusable Grazie browser credentials

Official [installation instructions](https://www.jetbrains.com/help/grazie-browser-extension/installation-guide.html)
support extension sign-in with a JetBrains Account. Its
[Text Playground](https://www.jetbrains.com/help/grazie-browser-extension/text-playground.html)
is a draft editor. No supported password/API-token proofreading flow has been
verified here; do not invent one or confuse unrelated JetBrains AI API tokens
with Grazie proofreading access.

The concrete handoff is a dedicated persistent browser profile, not a password
in chat. Choose `GRAZIE_BROWSER_PROFILE` as an absolute directory outside any
repository and `CHROME_BIN` as the Chrome executable. Then run:

```sh
node scripts/grazie-session.cjs init \
  --profile-dir "$GRAZIE_BROWSER_PROFILE" --browser "$CHROME_BIN"
```

The launcher creates a private mode-700 profile and opens the official
extension listing. The user installs the extension, signs in normally (including
MFA), chooses the license if prompted, and opens an empty Text Playground.
Do not enable Sync or use unrelated accounts in this profile. Never overwrite
an existing Playground draft: it is stored locally and may survive restarts.

Subsequent runs reuse the browser-owned login with:

```sh
node scripts/grazie-session.cjs start \
  --profile-dir "$GRAZIE_BROWSER_PROFILE" --browser "$CHROME_BIN"
```

The agent needs only the profile path and local debugging address (default
port 9229), not the password, cookies, MFA codes or refresh tokens. The profile
itself is sensitive: do not copy, inspect, archive, sync or commit its contents.
Debugging grants control of the entire dedicated browser; keep it loopback-only,
use it only with trusted local processes and close it after collection.
If authentication expires or a challenge appears, stop and let the user sign
in again through the normal UI. The launcher never extracts credential stores.

`grazie.cjs MANIFEST.json RAW.json` requires the official extension's empty
Text Playground and active service worker, using `CDP_URL` (default loopback
port 9229). It inserts only masked `.input` strings through the editor. A live
authenticated pilot on 2026-10-16 verified the extension's own POST to
`https://api.jetbrains.ai/user/v5/gec/correct/v4`, HTTP 200, and sentence-level
grammar results. This observed endpoint is NOT a public API contract: the
collector never calls it directly or reads/replays its authentication headers.
It retains only matching proofreading responses, statuses and safe endpoint
metadata, not unrelated traffic. Extension updates can require adapter changes.

Each accepted response must cover the entire exact submitted prose, accounting
only for the Playground's list/emphasis marker removal. `grazie-normalize.py`
maps sentence-relative UTF-16 replacement offsets back to masked input and
retains original source offsets/line flow. Display-only `Context` parts are not
edits. First offered fixes become separate proposals; all alternatives remain
in raw evidence. Warnings without fixes remain in the audit, not invented edits.
Inspect retained suggestions for technical false positives, especially grammar
rules that misunderstand mathematical usage (e.g. “associates to the left”).

The collector checkpoints each result and clears only its own unchanged draft.
It stops at failed HTTP responses or external draft changes. Inputs without a
complete matching response are explicitly unverified, never “no issues”; after
three such inputs it stops for inspection. Cached or placeholder-only inputs
may produce no new cloud request. Preserve partial evidence, and do not infer
whole-paper coverage from a successful login or pilot. No automatic retry loop
or credential access is provided.

## Preparing inputs

Prepare one unwrapped input per prose block. Markdown code fences, raw
offside math/BNF/TikZ blocks, TeX display environments and metadata are excluded.
Inline `$…$`, references and macros are indivisible placeholders; punctuation
and suffixes remain outside them. Literal code is not prose. Inspect rejected
or unknown syntax rather than treating the scanner as a general TeX parser.
If a paragraph exceeds a service limit, stop and split at verified sentence
boundaries, keeping offsets, not at arbitrary character/line boundaries.

## Adapter protocol

`review.py collect --manifest M.json --provider NAME --command 'program args'
--output R.json` sends the manifest JSON on stdin to an explicit command,
without a shell. It expects JSON with `source_sha256`, `provider`, optional
`engine`, and `records` entries containing unchanged `id` and `input` plus
the actual returned `output`. A provider name is provenance, not evidence of
authentication; keep cloud execution evidence in a separate artifact.
Do not label an unauthenticated/local adapter “Grazie cloud”. A cloud grammar
finding can be represented as a complete corrected paragraph obtained by
applying the provider's exact offsets/replacements to its exact submitted text;
do not invent a replacement for a warning without one. Use `note` for those.
Send only each record's `input` field to the external service, not its raw
`source`, reverse `mapping` or the whole manifest. Keep these locally.

`deepl.cjs MANIFEST.json RESULTS.json` uses `CDP_URL` (default localhost:9228),
requires exactly one DeepL Write page in that dedicated browser, and keeps
one input paragraph per request. A `ws` Node module must already be available.
Choose language/style in the UI first; the script does not assume Oxford
support or modify account settings. It requires an empty source editor so it
cannot overwrite somebody's draft. On completion it clears its own input.
It checks current editor content, placeholder provenance and a stable output;
it stops at auth/quota/challenge failures. Read the saved status of every
record. Missing placeholders may mean a bad rewrite, not a service error;
the report renderer rejects such a record. Do not retry failures indefinitely.

## Importing earlier evidence

`review.py import-legacy --source SOURCE --deepl OLD.json --grazie OLD.json
--output RESULTS.json` accepts the PTS-rk 49-batch evidence layout. It only
aligns batches with exactly matching paragraph counts; changed paragraph/list
structure is omitted, not guessed. The source hash must agree. Local Grazie
warnings remain labelled local and are never upgraded to cloud results.

## Review checks

Combine independently collected provider files before rendering:

```sh
python3 scripts/review.py merge deepl-results.json grazie-results.json \
  --output combined-results.json
python3 scripts/review.py render --source paper-markdown.tex \
  --results combined-results.json --names protected-names.txt \
  --terms protected-terms.txt --output WORDING_SUGGESTIONS.md
```

Merge rejects different source hashes and leaves the raw provider files intact.
If a successful, verified collection supersedes an old unavailable-service
note, remove that note in the combined review input, not in historical evidence.
Rendering deduplicates identical restored CriticMarkup at the same source span,
even when providers use different placeholder IDs. The single entry attributes
both providers. Distinct or partially overlapping rewrites remain alternatives;
do not splice them into an unsupported combined suggestion. Do not overwrite
coauthor review comments without first inspecting the report's current diff.
For conciseness, independent non-overlapping edits by the same provider(s)
at the same source span are shown together. This never merges conflicting
alternatives or changes an edit's provider attribution.

Compare source SHA256, paragraph IDs, exact inputs and preserved placeholders.
Audit normalized Oxford variants, project term sequences, ignored false
positives and ambiguous source mappings. Report only retained prose edits;
save exclusions/counts in a separate JSON audit, not a rejected-examples section.
Verify CriticMarkup accept/reject behavior and unchanged source files. Retain
the source's paragraph line breaks; if a changed span crosses a newline,
keep the old side verbatim and align the new side to those original breaks.

CriticMarkup syntax and single-block limitations follow the
[MultiMarkdown documentation](https://fletcher.github.io/MultiMarkdown-6/syntax/critic.html).
Source offsets use Python character indices; adapters using UTF-16 must
convert offsets on the submitted string before constructing replacements.

Publication gate: audit both providers' retained edits for proper names and
technical terminology, not only known spelling false positives. Build the
name inventory from the actual authors/citations/prose (including names at
sentence starts and possessives) and the glossary from the actual definitions.
Use `--names`/`--terms` in every render. Changing “Coquand's” to “Copland's”
is a rejected identity change, not an English improvement. Likewise reject
rewrites of technical words, not merely formulas: “least”, “iff”, “strictify”,
“greedily”, numerals, predicates and named calculi can carry formal meaning.
Do not assume a finite inventory guarantees detection of every new term:
inspect the final CriticMarkup, extend inventories, and rerender. Raw evidence
must remain unchanged so filtering decisions are reproducible.
