#!/usr/bin/env python3
"""Read-only import closure estimate; fresh Dune/.vo auditing is decisive."""
import collections
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
NAMESPACES = {
    "PTSrk.SelfConsistency": "theories/self_consistency",
    "PTSrk.SelfInterpreter": "theories/self_interpreter",
    "PTSrk.Combinatory": "theories/CombinatoryLogic-rk",
    "PTSrk.NormalizationComplexity": "theories/NormalizationComplexity",
    "Interpretation_of_R": "theories/Interpretation_of_R",
    "PTSrk": "theories",
}
OBJECT_ROOTS = [ROOT / "_build/default", pathlib.Path("/tmp/pts-rk-raw-internal.Cw6I7V/default")]


def without_comments(text):
    output, pos, depth = [], 0, 0
    while pos < len(text):
        if text.startswith("(*", pos):
            depth += 1; pos += 2
        elif text.startswith("*)", pos) and depth:
            depth -= 1; pos += 2
        else:
            if not depth:
                output.append(text[pos])
            pos += 1
    if depth:
        raise ValueError("unclosed source comment")
    return "".join(output)


def resolve(name):
    for namespace, folder in NAMESPACES.items():
        if name.startswith(namespace + "."):
            relative = pathlib.Path(folder) / (name[len(namespace) + 1:].replace(".", "/") + ".v")
            if not (ROOT / relative).is_file():
                raise ValueError("missing imported source: " + name + " -> " + str(relative))
            return relative
    return None


def dependencies(path):
    text = without_comments((ROOT / path).read_text())
    text = re.sub(r"-\([^)]*\)", "", text)
    result = []
    pattern = r"(?m)^\s*(?:From\s+([A-Za-z0-9_.]+)\s+)?Require\s+(?:(?:Import|Export)\s+)?([^;]+?)\.(?=\s|$)"
    for match in re.finditer(pattern, text):
        prefix = (match.group(1) + ".") if match.group(1) else ""
        for module in match.group(2).split():
            resolved = resolve(prefix + module)
            if resolved is not None:
                result.append(resolved)
    return result


def main():
    pending = [pathlib.Path(arg) for arg in sys.argv[1:]]
    if not pending:
        raise ValueError("supply existing root source paths")
    seen = set()
    while pending:
        path = pending.pop()
        if path not in seen:
            seen.add(path)
            pending.extend(dependencies(path))
    total_sources, total_objects, missing = 0, 0, []
    groups = collections.Counter()
    for path in sorted(seen):
        groups[str(path.parent)] += 1
        source_size = (ROOT / path).stat().st_size
        total_sources += source_size
        candidates = [directory / path.with_suffix(".vo") for directory in OBJECT_ROOTS]
        candidates = [obj for obj in candidates if obj.is_file()]
        size = max((obj.stat().st_size for obj in candidates), default=0)
        total_objects += size
        if not candidates:
            missing.append(str(path))
        print("%9d %9d %s" % (source_size, size, path))
    print("Native import closure estimate:", len(seen), "modules; source bytes:", total_sources)
    print("Existing object bytes (partial, not an upper bound):", total_objects)
    for group, count in sorted(groups.items()):
        print("%3d %s" % (count, group))
    print("Missing compiled objects:")
    print("\n".join(missing))
    print("External Stdlib/Equations and build metadata are excluded; this is not proof verification.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError) as error:
        print("FAIL:", error, file=sys.stderr)
        sys.exit(1)
