#!/usr/bin/env python3
"""Check body content and ordered mathematics against the traditional paper.

This is a source-level regression check, not a PDF/layout equivalence proof.
The body stream ignores formatting commands, whitespace and punctuation.
Formula comparison normalizes Unicode aliases, whitespace, equivalent display
wrappers and the requested PTS-rk prose-name macro, not mathematical content.
"""
from pathlib import Path
import difflib
import re
import argparse
import json
import sys
from paper_math import normalize_notation
sys.path.insert(0,str(Path(__file__).resolve().parent/'prose-review/scripts'))
from split_minor import restore_minor


def expand_formalization_links(source):
    """Resolve badge links, preserving their assistant and pinned URL."""
    header, body = source.split(":::Abstract", 1)
    roots = {}
    in_roots = False
    for line in header.splitlines():
        if line == 'formalization:':
            in_roots = True
        elif in_roots and line.startswith(' '):
            match = re.fullmatch(r'\s+([a-z][a-z0-9-]*):\s*(https?://\S+)', line)
            if not match or match[1] in roots:
                raise ValueError('Invalid or duplicate formalization root: ' + line)
            roots[match[1]] = match[2]
        else:
            in_roots = False

    def resolve(match):
        command, key, path = match.groups()
        if key not in roots or not path:
            raise ValueError('Unknown formalization root or empty path: ' + match[0])
        url = path if re.match(r'https?://', path) else roots[key] + path
        assistant = key.split('-')[0]
        legacy = assistant + ('formalised' if command == 'formalized' else 'proof')
        return '\\' + legacy + '{' + url + '}'

    body = re.sub(r'\\(formalized|proof)\{([^:{}]+):([^{}]*)\}', resolve, body)
    if re.search(r'\\(?:formalized|proof)\{', body):
        raise ValueError('Malformed formalization badge')
    return body


def native_tex(text):
    """Expand the documented MLTT-S constructs for source comparison."""
    text = re.sub(r"(?m)^> ?", "", text)
    text = re.sub(
        r"(?m)^:::Figure(?:\[[^\]]*\])? (.*?)\n([\s\S]*?)^:::[ \t]*$",
        lambda m: m[2] + r"\caption{" + m[1] + "}", text,
    )
    text = re.sub(r"(?m)^```[^\n]*\n([\s\S]*?)^```[ \t]*$",
                  lambda m: m[1], text)
    lines, expanded = text.splitlines(keepends=True), []
    i = 0
    while i < len(lines):
        match = re.match(r"^( *)%(mathpar|bnf|align\*?|gather\*?|multline\*?|tikzcd)\s*$", lines[i])
        if not match:
            expanded.append(lines[i]); i += 1; continue
        indent, name = len(match[1]), match[2]
        expanded.append(r"\begin{" + name + "}\n")
        i += 1
        while i < len(lines):
            line = lines[i]
            if line.strip() and len(line)-len(line.lstrip()) <= indent:
                break
            expanded.append(line); i += 1
        expanded.append(r"\end{" + name + "}\n")
    text = "".join(expanded)
    text = re.sub(r"%([A-Za-z]+|[^\s])", lambda m: "\\" + m[1], text)
    text = re.sub(r"\[(@[^\]]+)\]", lambda m: citation_tex(m[1]), text)
    text = re.sub(r"<#([^>]+)>", lambda m: r"\ref{" + m[1] + "}", text)
    text = re.sub(r"<((?:https?://)[^>]+)>", lambda m: r"\url{"+m[1]+"}", text)
    text = re.sub(r"\[([^\]]+)\]\((https?://[^)]+)\)",
                  lambda m: r"\href{"+m[2]+"}{"+m[1]+"}", text)
    text = re.sub(r"\{#[^}]+\}", "", text)
    text = re.sub(r"(?m)^\s*\d+\. ", "", text)
    return text


def citation_tex(text):
    keys = re.findall(r"@([A-Za-z0-9_:\-]+)", text)
    note = text.split(",", 1)[1] if "," in text else ""
    return r"\cite" + ("["+note+"]" if note else "") + "{"+",".join(keys)+"}"


def normalize_spelling(text):
    text = normalize_notation(text)
    # Expand only the newly requested prose name, not mathematical \PTS terms.
    text = text.replace(r"PTS-\texorpdfstring{$rk$}{rk}", "PTSrkNAME")
    text = text.replace("PTS-$rk$", "PTSrkNAME")
    text = text.replace(r"$\PTS$", "PTSrkNAME")
    text = re.sub(r"\\PTSrk(?:\{\})?", "PTSrkNAME", text)
    symbols = {
        'Γ':'Gamma', 'Δ':'Delta', 'Π':'Pi', 'λ':'lambda', 'β':'beta', 'α':'alpha',
        'κ':'kappa', 'ω':'omega', 'ℵ':'aleph', 'ε':'varepsilon',
        '→':'to', '⇒':'Rightarrow', '↔':'leftrightarrow', '↦':'mapsto',
        '⊢':'vdash', '∈':'in', '∉':'notin', '∀':'forall', '∃':'exists',
        '≤':'le', '≥':'ge', '≠':'neq', '×':'times', '⊆':'subseteq',
        '⊂':'subset', '∪':'cup', '∩':'cap', '∧':'land', '∨':'lor',
        '¬':'neg', '⋅':'cdot', '≜':'triangleq', '⇉':'rightrightarrows',
        '∞':'infty', '≡':'equiv', 'ℓ':'ell', 'ν':'nu', 'ρ':'rho', 'δ':'delta',
        '□':'square', '△':'triangle', '⇔':'Leftrightarrow',
        '↝':'leadsto', '⦇':'llparenthesis', '⦈':'rrparenthesis',
        '⟦':'llbracket', '⟧':'rrbracket', '⟨':'langle', '⟩':'rangle',
        'σ':'sigma', 'Ω':'Omega', 'φ':'varphi', '⊥':'bot', '⊤':'top',
        '∘':'circ', '∅':'varnothing', '≔':'coloneqq', '↑':'uparrow',
        '⟶':'longrightarrow', '⟺':'Longleftrightarrow', '⊔':'sqcup',
        '≃':'simeq', '⊬':'nvdash', '⋯':'cdots', '…':'ldots',
        '∏':'prod', '⋁':'bigvee',
    }
    for char, macro in symbols.items():
        text = text.replace(char, "\\"+macro+" ")
    for char, letter in [('ℕ','N'),('ℤ','Z'),('ℚ','Q'),('ℝ','R')]:
        text = text.replace(char, r"\mathbb{"+letter+"}")
    text = text.replace('∗','*').replace('ö',r'\"{o}').replace('ï',r'\"{i}')
    text = re.sub(r"\\mathbb\s+([NZQR])\b", r"\\mathbb{\1}", text)
    aliases = {'leq':'le', 'geq':'ge', 'ne':'neq', 'wedge':'land', 'vee':'lor', 'rightarrow':'to'}
    text = re.sub(r"\\([A-Za-z]+)", lambda m: "\\"+aliases.get(m[1],m[1]), text)
    text = text.replace(r"\eqref{", r"\ref{")
    text = text.replace(r"\(", "$").replace(r"\)", "$")
    text = re.sub(r"\[ampersand replacement\s*=\s*\\&\]", "", text)
    # A literal \& in tikzcd is not the tail of the row break \\& in align.
    text = re.sub(r"(?<!\\)\\&", "&", text)
    text = text.replace('“', '``').replace('”', "''")
    # mathpar and standalone tikzcd provide their own display math wrapper.
    text = re.sub(r"\\begin\{mathpar\}([\s\S]*?)\\end\{mathpar\}",
                  lambda m: r"\["+m[1]+r"\]", text)
    text = re.sub(r"(?<!\[)\\begin\{tikzcd\}([\s\S]*?)\\end\{tikzcd\}",
                  lambda m: r"\[\begin{tikzcd}"+m[1]+r"\end{tikzcd}\]", text)
    for original, inner in [('align','aligned'), ('gather','gathered'), ('multline','multlined')]:
        text = re.sub(r"\\\[\s*\\begin\{"+inner+r"\}([\s\S]*?)\\end\{"+inner+r"\}\s*\\\]",
                      lambda m: r"\begin{"+original+"*}"+m[1]+r"\end{"+original+"*}", text)
    return text


def unwrap_markdown(text):
    # Do not interpret TeX quotation marks inside raw blocks as code spans.
    parts = re.split(r"(?m)^```\{=tex\}\n([\s\S]*?)^```[ \t]*$", text)
    for i in range(0, len(parts), 2):
        parts[i] = re.sub(
            r"(`+)(.*?)\1\{=tex\}", lambda m: m[2], parts[i], flags=re.S
        )
    text = "".join(parts)
    text = re.sub(
        r"^:::\w+(?:\[(.*)\])?(?: \{#[^}]+\})?\s*$",
        lambda m: m[1] or "", text, flags=re.M,
    )
    text = re.sub(r"^:::\s*$", "", text, flags=re.M)
    text = re.sub(r"^#+ ", "", text, flags=re.M)
    return text.replace("^[", "[")


def body_stream(text):
    text = re.sub(r"(?<!\\)%[^\n]*", "", text)
    text = re.sub(r"\\vspace\*?\{[-+]?(?:\d+(?:\.\d+)?|\.\d+)(?:em|ex|pt)\}", "", text)
    text = re.sub(
        r"\\(?:begin|end)\{(?:abstract|theorem\*?|lemma|definition|"
        r"proposition|corollary|remark|proof)\}", "", text,
    )
    text = re.sub(r"\\label\{[^}]*\}", "", text)
    text = re.sub(r"\\begin\{figure\}\[[^\]]*\]", "", text)
    text = re.sub(r"\\(?:begin|end)\{(?:itemize|enumerate|figure|quote|minted|verbatim)\}(?:\{(?:coq|agda)\})?", "", text)
    text = re.sub(r"\\(?:item|caption)\b", "", text)
    text = re.sub(
        r"\\(?:section|subsection|subsubsection|paragraph|emph|textit|"
        r"textbf|footnote)\*?", "", text,
    )
    text = text.replace('\\"', "").replace("“", "").replace("”", "")
    return "".join(c for c in text if c.isalnum() or c == "\\")


def mathematics(text):
    pattern = re.compile(
        r"(?<!\\)\$(?:\\.|[^$])*\$|\\\([\s\S]*?\\\)|"
        r"\\\[[\s\S]*?\\\]|\\begin\{"
        r"(mathpar|align\*?|equation\*?|gather\*?|multline\*?)"
        r"\}[\s\S]*?\\end\{\1\}"
    )
    def canonical_math(s):
        for original, inner in [('align','aligned'), ('gather','gathered'), ('multline','multlined')]:
            s = re.sub(r"\\\[\s*\\begin\{"+inner+r"\}([\s\S]*)\\end\{"+inner+r"\}\s*\\\]",
                       lambda m: r"\begin{"+original+"*}"+m[1]+r"\end{"+original+"*}", s)
        s = re.sub(r"(?<!\\)\\&", "&", s.replace(r"[ampersand replacement=\&]", ""))
        return re.sub(r"\s+", "", s)
    return [canonical_math(m[0]) for m in pattern.finditer(text)]


def approved_math_baseline(fragments, edits):
    """Apply only explicitly recorded author changes to the expected formulas."""
    fragments = list(fragments)
    for edit in edits:
        if not edit.get('math_change'):
            continue
        before, after = [mathematics(normalize_spelling(value))
                         for value in (edit['before'], edit['after'])]
        positions = [i for i in range(len(fragments) - len(before) + 1)
                     if fragments[i:i + len(before)] == before]
        if not before or len(positions) != 1:
            raise ValueError('Missing/ambiguous approved mathematical baseline')
        i = positions[0]
        fragments[i:i + len(before)] = after
    return fragments


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rendered-dir", type=Path,
                        help="also reject escaped math or unintended code in parser output")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1] / "latex"
    original = (root / "paper.tex").read_text()
    original = original.split(r"\begin{abstract}", 1)[1]
    original = original.rsplit(r"\end{document}", 1)[0]
    markdown = (root / "PTS-rk.tex").read_text()
    actual_markdown = normalize_spelling(unwrap_markdown(expand_formalization_links(native_tex(markdown))))
    minor_report = root / 'MINOR_CORRECTIONS.md'
    if minor_report.exists():
        markdown = restore_minor(markdown,minor_report.read_text())
        print('Checked comma/article corrections: exact baseline restored for prose comparison')
    # Exact user-approved prose differences, not a general wording exemption.
    edits = json.loads((root / 'PROSE_EDITS.json').read_text())
    for edit in edits:
        if markdown.count(edit['after']) != 1:
            raise ValueError('Missing/ambiguous approved prose edit: ' + edit['after'])
        markdown = markdown.replace(edit['after'], edit['before'], 1)
    markdown = expand_formalization_links(native_tex(markdown))
    markdown = unwrap_markdown(markdown)
    original, markdown = map(normalize_spelling, (original, markdown))
    left, right = map(body_stream, (original, markdown))
    print("Canonical body characters:", len(left), len(right), "equal:", left == right)
    if left != right:
        for tag, i, j, k, l in difflib.SequenceMatcher(None, left, right).get_opcodes():
            if tag != "equal":
                print(tag, repr(left[max(0, i-40):j+40]),
                      "=>", repr(right[max(0, k-40):l+40]))
    # Always compare ACTUAL mathematics, never the prose-restored version.
    a, b = map(mathematics, (original, actual_markdown))
    a = approved_math_baseline(a, edits)
    print("Ordered math fragments:", len(a), len(b), "equal:", a == b)
    for i, (x, y) in enumerate(zip(a, b)):
        if x != y:
            print("Formula", i, repr(x), "!=", repr(y))
    rendered_ok = True
    if args.rendered_dir:
        files = sorted(args.rendered_dir.glob("*.md.tex"))
        if not files:
            print("No rendered Markdown files found:", args.rendered_dir)
            rendered_ok = False
        malformed = re.compile(
            r"\\markdownRenderer(?:Backslash|DollarSign)|"
            r"\\markdownRendererInputVerbatim|:::(?:Figure|Theorem|Lemma)"
            r"|^[ \t]*%(?:mathpar|align\*?|gather\*?|multline\*?|tikzcd)\s*$"
        )
        for file in files:
            rendered = file.read_text()
            for display in re.finditer(r"\\begin\{mathpar\}[\s\S]*?\\end\{mathpar\}", rendered):
                if 'This is true by structural induction' in display[0]:
                    print('Proof prose swallowed by mathpar:', file)
                    rendered_ok = False
            if re.search(
                r"\\markdownRenderer(?:Interblock|Paragraph)Separator\s*\{\}"
                r"\\begin\{(?:mathpar|align\*?|gather\*?|multline\*?|equation\*?)\}",
                rendered,
            ):
                print("Redundant paragraph separator before display:", file)
                rendered_ok = False
            for line, content in enumerate(rendered.splitlines(), 1):
                if malformed.search(content):
                    print("Unparsed native syntax:", file, line, content[:160])
                    rendered_ok = False
        expected_listings = len(re.findall(r"\\begin\{(?:minted|verbatim)\}", original))
        actual_listings = sum(file.read_text().count(r"\markdownRendererInputFencedCode")
                              for file in files)
        print("Source/rendered code listings:", expected_listings, actual_listings)
        rendered_ok = rendered_ok and expected_listings == actual_listings
        print("Rendered native-syntax check:", rendered_ok)
    return 0 if left == right and a == b and rendered_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
