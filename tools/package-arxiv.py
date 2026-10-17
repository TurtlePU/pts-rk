#!/usr/bin/env python3
"""Export the Markdown paper as cached, shell-free XeLaTeX for arXiv."""
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "latex"
WORK = Path(tempfile.mkdtemp(prefix="pts-rk-arxiv-"))
BUILD = WORK / "build"
PACKAGE = WORK / "package"
BUILD.mkdir()
PACKAGE.mkdir()
print(f"Build and verification logs: {WORK}", flush=True)


def run(command, cwd, log):
    print("Running:", " ".join(command), flush=True)
    with (WORK / log).open("w") as stream:
        result = subprocess.run(command, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT)
    if result.returncode:
        print((WORK / log).read_text(errors="replace")[-6000:])
        raise SystemExit(f"Command failed ({result.returncode}); see {WORK / log}")


def copy(source, destination):
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, destination)


# Snapshot dependencies, never edit the live manuscript or preamble.
for name in ("PTS-rk.tex", "markdown.cls", "markdown.sty", "verified-badges.sty",
             "bibliography.bib"):
    copy(PAPER / name, BUILD / name)
for name in ("tex", "markdown", "badges"):
    shutil.copytree(PAPER / name, BUILD / name)
snapshot = (BUILD / "PTS-rk.tex").read_bytes()
preamble_path = BUILD / "tex/preamble.tex"
preamble = preamble_path.read_text()
original_preamble = preamble
option = r"\PassOptionsToPackage{cachedir=minted-cache}{minted}"
preamble = preamble.replace(r"\usepackage" + "\n{amsmath", option + "\n\\usepackage\n{amsmath", 1)
if option not in preamble:
    raise SystemExit("Cannot locate minted package setup")
# Capture the class's actual metadata emission; don't maintain a second YAML parser.
capture = r'''
\AtBeginDocument{\directlua{
  local stream = assert(io.open("arxiv-metadata.tex", "w"))
  local original = tex.sprint
  tex.sprint = function(value) stream:write(value, string.char(10)) end
  markdownclass.emit_metadata()
  tex.sprint = original
  stream:close()
}}
'''
preamble_path.write_text(preamble + capture)
run(["latexmk", "-lualatex", "-interaction=nonstopmode", "-halt-on-error", "PTS-rk.tex"],
    BUILD, "cache-build.log")

# There is one top-level rendered body; input listings remain separate dependencies.
bodies = list((BUILD / "_markdown_PTS-rk").glob("*.md.tex"))
if len(bodies) != 1:
    raise SystemExit(f"Expected one rendered body, found {len(bodies)}")
body = bodies[0].read_text()
metadata = (BUILD / "arxiv-metadata.tex").read_text()
class_match = re.search(r"\\documentclass(?:\[[^\]]*\])?\{[^}]*\}", preamble)
if not class_match:
    raise SystemExit("Missing base document class")
base_class = class_match.group()
export_preamble = preamble[class_match.end():].replace(
    "cachedir=minted-cache", "frozencache=true,cachedir=minted-cache", 1)
copy_preamble = PACKAGE / "tex/preamble_precompiled.tex"
copy_preamble.parent.mkdir()
copy_preamble.write_text(export_preamble)
main = r'''% arXiv submission export: compile with XeLaTeX (TeX Live 2025).
% Markdown was rendered locally; minted uses only the supplied frozen cache.
''' + base_class + r'''
\usepackage{etoolbox,fontspec}
\setmainfont{lmroman10-regular.otf}[
  BoldFont=lmroman10-bold.otf, ItalicFont=lmroman10-italic.otf,
  BoldItalicFont=lmroman10-bolditalic.otf,
  SmallCapsFont=lmromancaps10-regular.otf,
  ItalicFeatures={SmallCapsFont=lmromancaps10-oblique.otf}]
\setsansfont{lmsans10-regular.otf}[BoldFont=lmsans10-bold.otf,
  ItalicFont=lmsans10-oblique.otf, BoldItalicFont=lmsans10-boldoblique.otf]
\setmonofont{lmmono10-regular.otf}[BoldFont=lmmonolt10-bold.otf,
  ItalicFont=lmmono10-italic.otf, BoldItalicFont=lmmonolt10-boldoblique.otf]
\makeatletter
\newdimen\markdownclass@dateskip
\let\markdownclass@dateprefix\@empty
\makeatother
\input{tex/preamble_precompiled.tex}
\renewcommand\Authsep{\protect\\}
\renewcommand\Authand{\protect\\}
\renewcommand\Authands{\protect\\}
\affilsep=.3\affilsep
\makeatletter
''' + metadata + r'''
\makeatother
\begin{document}
\maketitle
\begingroup
\catcode`\%=12\relax
\catcode`\#=12\relax
''' + body + "\n\\endgroup\n\\end{document}\n"
(PACKAGE / "PTS-rk_precompiled.tex").write_text(main)
copy(BUILD / "PTS-rk.bbl", PACKAGE / "PTS-rk_precompiled.bbl")
for name in ("markdown.sty", "verified-badges.sty", "bibliography.bib"):
    copy(BUILD / name, PACKAGE / name)
# The fork preloads its Lua parser unconditionally. The export uses only
# renderer macros, so skip that loader under XeTeX (no parser invocation).
style_path = PACKAGE / "markdown.sty"
style = style_path.read_text()
style = style.replace("\\directlua{", "\\ifdefined\\directlua\n\\directlua{", 1)
style = style.replace("\\input markdown/markdown", "\\fi\n\\input markdown/markdown", 1)
style_path.write_text(style)
# Freeze the minted/cache protocol too: installed minted 3.8 requires the
# 2026 latex2pydata helper, which arXiv's TeX Live 2025 does not contain.
# Both files carry their original redistribution/license headers.
for name in ("minted.sty", "latex2pydata.sty"):
    installed = subprocess.check_output(["kpsewhich", name], text=True).strip()
    copy(Path(installed), PACKAGE / name)
# Rendering macros are needed, but not the Lua parser or metadata class.
for name in ("markdown.tex", "markdownthemewitiko_markdown_defaults.sty",
             "markdownthemewitiko_markdown_defaults.tex"):
    copy(BUILD / "markdown" / name, PACKAGE / "markdown" / name)
for name in re.findall(r"\\markdownRendererInputFencedCode\{([^}]+)\}", body):
    copy(BUILD / name, PACKAGE / name)
# Include only cache/artwork inputs actually read in the successful build.
for line in (BUILD / "PTS-rk.fls").read_text().splitlines():
    if not line.startswith("INPUT "):
        continue
    name = line[6:].removeprefix("./")
    if name.startswith(("badges/", "minted-cache/")):
        copy(BUILD / name, PACKAGE / name)
if not list((PACKAGE / "minted-cache").glob("*.highlight.minted")):
    raise SystemExit("No minted highlighting cache generated")

# Preserve the exact editable source and its custom build dependencies for
# readers, beside the pre-rendered submission entry point.
original = PACKAGE
for name in ("PTS-rk.tex", "markdown.cls"):
    copy(BUILD / name, original / name)
(original / "tex/preamble.tex").write_text(original_preamble)
for path in (BUILD / "markdown").iterdir():
    if path.suffix in (".tex", ".sty", ".lua") or path.name == "PROVENANCE.md":
        copy(path, original / "markdown" / path.name)
(original / "README.md").write_text(
    "# Original editable manuscript\n\n"
    "PTS-rk.tex is the byte-for-byte original Markdown–TeX manuscript.\n"
    "Its unmodified preamble, metadata class and custom Markdown runtime\n"
    "are included here. To rebuild locally with LuaLaTeX, Biber and minted\n"
    "(tested with TeX Live 2026), run:\n\n"
    "    latexmk -lualatex -interaction=nonstopmode -halt-on-error PTS-rk.tex\n\n"
    "PTS-rk_precompiled.tex is the pre-rendered XeLaTeX submission copy,\n"
    "which uses the supplied frozen minted cache without shell execution.\n"
    "PTS-rk_precompiled.bbl is the precompiled bibliography: no Biber run\n"
    "is required for this submission entry point.\n"
    "00README.json selects only that file for arXiv compilation; these\n"
    "settings can instead be selected in arXiv's Review Files interface.\n")
directives = {
    "spec_version": 1,
    "process": {"compiler": "xelatex"},
    "sources": [{"filename": "PTS-rk_precompiled.tex", "usage": "toplevel"}] + [
        {"filename": str(path.relative_to(PACKAGE)), "usage": "include"}
        for path in sorted(PACKAGE.rglob("*"))
        if path.is_file() and path.name != "PTS-rk_precompiled.tex"
    ],
}
(PACKAGE / "00README.json").write_text(json.dumps(directives, indent=2) + "\n")

# Test the exact archive, extracted into a clean directory: no aux/log/parser
# caches and no external commands. The included bbl avoids a Biber dependency.
archive = WORK / "PTS-rk-arxiv.zip"
with zipfile.ZipFile(archive, "w", zipfile.ZIP_DEFLATED) as bundle:
    for path in sorted(PACKAGE.rglob("*")):
        if path.is_file():
            bundle.write(path, path.relative_to(PACKAGE))
verify = WORK / "verify"
with zipfile.ZipFile(archive) as bundle:
    bundle.extractall(verify)
assert (verify / "PTS-rk.tex").read_bytes() == snapshot
assert (verify / "tex/preamble.tex").read_text() == original_preamble
for attempt in range(1, 4):
    run(["xelatex", "-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error",
         "-recorder", "PTS-rk_precompiled.tex"], verify, f"frozen-build-{attempt}.log")
log = (verify / "PTS-rk_precompiled.log").read_text(errors="replace")
if any(message in log for message in ("There were undefined references", "undefined on input line",
                                      "Please (re)run Biber", "Rerun to get cross-references right")):
    raise SystemExit("Frozen build has unresolved references; inspect verification logs")
if (PAPER / "PTS-rk.tex").read_bytes() != snapshot:
    raise SystemExit("Manuscript changed during packaging; rerun before publishing artifacts")
manifest = "\n".join(str(p.relative_to(PACKAGE)) for p in sorted(PACKAGE.rglob("*")) if p.is_file())
(WORK / "manifest.txt").write_text(manifest + "\n")
copy(BUILD / "PTS-rk.pdf", PAPER / "PTS-rk.pdf")
copy(archive, PAPER / archive.name)
print(f"Archive: {PAPER / archive.name}")
print(f"SHA256: {hashlib.sha256(archive.read_bytes()).hexdigest()}")
print(f"Frozen XeLaTeX verification PDF: {verify / 'PTS-rk_precompiled.pdf'}")
print(f"Contents:\n{manifest}")
