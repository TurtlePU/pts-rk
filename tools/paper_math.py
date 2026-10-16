"""Presentation-only notation and whitespace normalization for the paper.

Literal listings, metadata, prose, text-macro arguments and TeX spacing commands
are not mathematics to rewrite. Script arguments are consumed before binary
operators are spaced, so e.g. →_β^∗ and N^+ remain attached.
"""
import re
import textwrap


def argument(s, i):
    while i < len(s) and s[i].isspace():
        i += 1
    if i == len(s):
        raise ValueError('Missing TeX argument')
    if s[i] != '{':
        m = re.match(r'\\(?:[A-Za-z]+|.)|.', s[i:])
        return m[0], i + len(m[0]), False
    start, depth = i + 1, 1
    i += 1
    while i < len(s):
        if s[i] == '\\':
            m = re.match(r'\\(?:[A-Za-z]+|.)', s[i:])
            i += len(m[0])
            continue
        if s[i] == '{':
            depth += 1
        elif s[i] == '}':
            depth -= 1
            if not depth:
                return s[start:i], i + 1, True
        i += 1
    raise ValueError('Unclosed TeX argument')


def normalize_notation(s):
    pattern = re.compile(r'\\mathsf\{rk\}\s*_|\\mathcal\{N\}\s*_|\\rk(?![A-Za-z])|\\chNat(?![A-Za-z])')
    out, end = [], 0
    for m in pattern.finditer(s):
        if m.start() < end:
            continue
        value, stop, _ = argument(s, m.end())
        name = 'chNat' if 'N' in m[0] else 'rk'
        out.extend((s[end:m.start()], '\\' + name + '{' + normalize_notation(value) + '}'))
        end = stop
    out.append(s[end:])
    return ''.join(out)


OPS = set('=:+-−×∪∩∧∨↔⇔→⇒↦⊢∈∉≤≥≠⊆⊂≡≜⋅⊔<>⇉↝∘≔↑⟶⟺≃⊬&')
BINARY = {'ac', 'oc', 'iffc', 'colon', 'mid', 'sim', 'simeq', 'cong', 'approx'}
SPACING = {'quad', 'qquad'}
TEXT = {'text', 'textrm', 'textsf', 'textsc', 'texttt', 'mathrm', 'mathsf',
        'mathcal', 'mathtt', 'operatorname', 'label', 'tag', 'begin', 'end'}


def formula(s):
    out, i = '', 0
    while i < len(s):
        c, name = s[i], ''
        j = i + 1
        if c == '\\':
            m = re.match(r'\\([A-Za-z]+|.)', s[i:], re.S)
            token, name = m[0], m[1]
            j = i + len(token)
            if name in TEXT:
                k = j
                while k < len(s) and s[k] in ' \t':
                    k += 1
                if k < len(s) and s[k] == '{':
                    _, j, _ = argument(s, k)
                    token = s[i:j]
        elif c == '{':
            value, j, _ = argument(s, i)
            token = '{' + formula(value) + '}'
        elif c in '_^':
            value, j, braced = argument(s, j)
            token = c + ('{' + formula(value) + '}' if braced else value)
            out = out.rstrip(' \t') + token
            i = j
            continue
        else:
            token = c
        if c in OPS or name in BINARY or name in SPACING:
            # The operator plus all its scripts is one source token.
            while True:
                k = j
                while k < len(s) and s[k].isspace():
                    k += 1
                if k == len(s) or s[k] not in '_^':
                    break
                value, j, braced = argument(s, k + 1)
                token += s[k] + ('{' + formula(value) + '}' if braced else value)
            unary = c in '+-−' and (not out.strip() or out.rstrip()[-1] in '([{,:=→⇒')
            line = out.rsplit('\n', 1)[-1]
            out = out.rstrip(' \t') if line.strip() else out
            out += ('' if unary or not line.strip() else ' ') + token
            if not unary:
                out += ' '
            i = j
            while i < len(s) and s[i] in ' \t':
                i += 1
            continue
        if c == ',':
            out = out.rstrip(' \t') + ', '
            i = j
            while i < len(s) and s[i] in ' \t':
                i += 1
            continue
        if c in ' \t':
            line = out.rsplit('\n', 1)[-1]
            if not line.strip() or not out.endswith(' '):
                out += c
        else:
            out += token
        i = j
    return '\n'.join(line.rstrip() for line in out.split('\n')).strip()


def math_layout(s):
    """Align nested environments and multiline fractions in offside math."""
    # Keep short rules compact, but put multiple premises and their conclusion
    # in separate aligned arguments rather than wrapping through both braces.
    out, stop = [], 0
    for m in re.finditer(r'\\inferrule(?:\[[^\]]*\])?', s):
        if m.start() < stop:
            continue
        first, mid, _ = argument(s, m.end())
        second, end, _ = argument(s, mid)
        if '\\\\' not in first and '\n' not in first:
            continue
        indent = re.match(r' *', s[s.rfind('\n', 0, m.start()) + 1:])[0]
        first = re.sub(r'\s*\\\\\s*', lambda _: ' \\\\ ', first)
        first = re.sub(r'\s+', ' ', first).strip()
        second = re.sub(r'\s+', ' ', second).strip()
        out.extend((s[stop:m.start()], m[0] + '\n' + indent + '  {' +
                    first + '}\n' + indent + '  {' + second + '}'))
        stop = end
    out.append(s[stop:])
    s = ''.join(out)
    # Keep the two arguments together visually, with matching opening braces.
    out, stop = [], 0
    for m in re.finditer(r'\\dfrac(?![A-Za-z])', s):
        if m.start() < stop:
            continue
        first, mid, _ = argument(s, m.end())
        second, end, _ = argument(s, mid)
        if '\n' not in s[m.start():end]:
            continue
        indent = re.match(r' *', s[s.rfind('\n', 0, m.start()) + 1:])[0]
        args = []
        for value in (first, second):
            rows = value.strip().splitlines()
            args.append('{' + ('\n' + indent + '       ').join(row.strip() for row in rows) + '}')
        out.extend((s[stop:m.start()], '\\dfrac' + args[0] +
                    '\n' + indent + '      ' + args[1]))
        stop = end
    out.append(s[stop:])
    s = ''.join(out)
    # Put environment boundaries at the start of a line so their matching
    # indentation is visible even after an opening delimiter or implication.
    s = re.sub(r'(?m)^( *)(\S[^\n]*?)(\\begin\{[^}]+\})',
               lambda m: m[1] + m[2].rstrip() + '\n' + m[1] + m[3], s)
    rows, stack = [], []
    for line in s.splitlines():
        stripped = line.lstrip()
        closing = re.match(r'\\end\{([^}]+)\}', stripped)
        if closing:
            if not stack or stack[-1][0] != closing[1]:
                raise ValueError('Mismatched math environment: ' + stripped)
            _, indent, _ = stack.pop()
            line = ' ' * indent + stripped
        elif stack:
            # Escaped set braces can contain several continuation lines.
            before = 1 if stripped.startswith(r'\}') else 0
            depth = max(0, stack[-1][2] - before)
            line = ' ' * (stack[-1][1] + 2 + 2 * depth) + stripped
            stack[-1][2] = max(0, stack[-1][2] +
                               len(re.findall(r'\\\{', stripped)) -
                               len(re.findall(r'\\\}', stripped)))
        elif re.match(r'\\begin\{', stripped):
            line = stripped
        opening = re.match(r'\\begin\{([^}]+)\}', line.lstrip())
        if opening:
            stack.append([opening[1], len(line) - len(line.lstrip()), 0])
        # A leading row break gets its own line, not a new formula after it.
        leading = re.match(r'^( *)\\\\\s+(\S.*)$', line)
        if leading:
            rows.extend((leading[1] + '\\\\', leading[1] + leading[2]))
        else:
            rows.append(line)
    if stack:
        raise ValueError('Unclosed math environment: ' + stack[-1][0])
    return '\n'.join(rows)


def format_source(s):
    # Keep literal Coq, Agda and quoted prompt listings byte-for-byte.
    parts = re.split(r'(?m)^((?:> )?```[^\n]*\n[\s\S]*?^(?:> )?```[^\n]*$)', s)
    for n in range(0, len(parts), 2):
        text = normalize_notation(parts[n])
        text = re.sub(r'(?<!\\)\$(?:\\.|[^$])*\$',
                      lambda m: '$' + formula(m[0][1:-1]) + '$', text)
        text = re.sub(r'\\\[([\s\S]*?)\\\]',
                      lambda m: '\\[\n' + textwrap.indent(formula(textwrap.dedent(m[1])), '    ') + '\n  \\]', text)
        lines, out, i = text.splitlines(keepends=True), [], 0
        while i < len(lines):
            m = re.match(r'^( *)%(mathpar|align\*?|gather\*?|multline\*?|tikzcd)\s*$', lines[i])
            if not m:
                out.append(lines[i]); i += 1
                continue
            base = len(m[1])
            out.append(lines[i]); i += 1
            body = []
            while i < len(lines) and (not lines[i].strip() or len(lines[i])-len(lines[i].lstrip()) > base):
                body.append(lines[i]); i += 1
            out.append(textwrap.indent(math_layout(formula(textwrap.dedent(''.join(body)))), ' ' * (base + 2)) + '\n')
            if body and not body[-1].strip():
                out.append('\n')
        parts[n] = ''.join(out)
    return ''.join(parts)
