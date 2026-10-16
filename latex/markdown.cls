\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{markdown}[2026/06/25 Lua Markdown document class]

\RequirePackage{kvoptions}

\SetupKeyvalOptions{
  family=markdownclass,
  prefix=markdownclass@
}

\DeclareStringOption{preamble}
\DeclareBoolOption[false]{authorsonlines}
% Recognize this boolean in the legacy bare-preamble option pass too.
\DeclareOption{authorsonlines}{\markdownclass@authorsonlinestrue}

% A storage macro for a single bare option such as:
%   \documentclass[preamble.tex]{markdown}
\def\markdownclass@barepreamble{}

% Pre-scan raw LaTeX class options.
% Anything containing "=" is left for kvoptions.
% A single non-keyval option is treated as the preamble file.
\DeclareOption*{%
  \def\markdownclass@tmpa{=}%
  \expandafter\markdownclass@option@has@equals\CurrentOption=\@nil
}

\def\markdownclass@option@has@equals#1=#2\@nil{%
  \def\markdownclass@tmpb{#2}%
  \ifx\markdownclass@tmpb\@empty
    % No "=" was found: this is the bare preamble filename.
    \ifx\markdownclass@barepreamble\@empty
      \edef\markdownclass@barepreamble{\CurrentOption}%
    \else
      \ClassError{markdown}
        {More than one bare option was given}
        {Use only one bare preamble file option, for example:
         \string\documentclass[preamble.tex]{markdown}.}%
    \fi
  \fi
}

\def\markdownclass@remove@unused@option#1{%
  \edef\markdownclass@remove@target{#1}%
  \let\markdownclass@newunused\@empty
  \@for\markdownclass@unused:=\@unusedoptionlist\do{%
    \edef\markdownclass@unused@expanded{\markdownclass@unused}%
    \ifx\markdownclass@unused@expanded\markdownclass@remove@target
    \else
      \ifx\markdownclass@newunused\@empty
        \xdef\markdownclass@newunused{\markdownclass@unused}%
      \else
        \xdef\markdownclass@newunused{\markdownclass@newunused,\markdownclass@unused}%
      \fi
    \fi
  }%
  \let\@unusedoptionlist\markdownclass@newunused
}

% Run the normal LaTeX option pass just to collect the bare option.
\ProcessOptions*\relax

% Now process key-value options such as preamble=...
\ProcessKeyvalOptions*

% If preamble=... was not supplied, use the bare option.
\ifx\markdownclass@preamble\@empty
  \ifx\markdownclass@barepreamble\@empty
  \else
    \let\markdownclass@preamble\markdownclass@barepreamble
  \fi
\fi

\ifx\markdownclass@barepreamble\@empty
\else
  \markdownclass@remove@unused@option{\markdownclass@barepreamble}%
\fi


\RequirePackage{iftex}
\RequireLuaTeX
\RequirePackage{luacode}

\makeatletter

\ifx\markdownclass@preamble\@empty
  \ClassError{markdown}
    {No preamble specified}
    {Use \string\documentclass[preamble=templates/preamble.tex]{markdown}.}%
\fi

\edef\markdownclass@strippedpreamble{\jobname.markdown.preamble.tex}
\edef\markdownclass@bodyfile{\jobname.markdown.body.md}

\begin{luacode*}
markdownclass = markdownclass or {}

local function readable(name)
  local f = io.open(name, "rb")
  if f then
    f:close()
    return true
  end
  return false
end

local function read_all(name)
  local f = assert(io.open(name, "rb"))
  local s = f:read("*a")
  f:close()
  return s
end

local function write_all(name, s)
  local f = assert(io.open(name, "wb"))
  f:write(s)
  f:close()
end

local function tex_escape(s)
  -- Intended for ordinary class names/options/file names.
  -- This is not a full TeX serializer for arbitrary active-character input.
  s = s:gsub("\\", "\\string\\")
  s = s:gsub("{", "\\string{")
  s = s:gsub("}", "\\string}")
  return s
end

local function skip_space_comments(s, i)
  while i <= #s do
    local c = s:sub(i, i)

    if c:match("%s") then
      i = i + 1
    elseif c == "%" then
      local j = s:find("\n", i + 1, true)
      if not j then
        return #s + 1
      end
      i = j + 1
    else
      return i
    end
  end

  return i
end

local function scan_balanced(s, i, open_char, close_char)
  local depth = 0
  local content_start = i + 1

  while i <= #s do
    local c = s:sub(i, i)

    if c == "\\" then
      -- Skip escaped/control sequence starter plus following character.
      -- Good enough for documentclass option parsing.
      i = i + 2
    elseif c == "%" then
      local j = s:find("\n", i + 1, true)
      if not j then
        return #s + 1, s:sub(content_start)
      end
      i = j + 1
    else
      if c == open_char then
        depth = depth + 1
      elseif c == close_char then
        depth = depth - 1
        if depth == 0 then
          return i + 1, s:sub(content_start, i - 1)
        end
      end

      i = i + 1
    end
  end

  error("markdown class: unterminated " .. open_char .. close_char)
end

local function parse_documentclass(s)
  local p = s:find("\\documentclass", 1, true)

  if not p then
    error("markdown class: cannot find \\documentclass")
  end

  local i = p + string.len("\\documentclass")
  local options = ""

  i = skip_space_comments(s, i)

  if s:sub(i, i) == "[" then
    local next_i, opt = scan_balanced(s, i, "[", "]")
    options = opt
    i = skip_space_comments(s, next_i)
  end

  if s:sub(i, i) ~= "{" then
    error("markdown class: cannot find mandatory class argument after \\documentclass")
  end

  local end_i, class = scan_balanced(s, i, "{", "}")

  return {
    start_pos = p,
    end_pos = end_i,
    options = options,
    class = class,
  }
end

function markdownclass.parse_preamble(preamble_name, stripped_name)
  if not readable(preamble_name) then
    error("markdown class: cannot open preamble file " .. preamble_name)
  end

  local s = read_all(preamble_name)
  local dc = parse_documentclass(s)

  local stripped = s:sub(dc.end_pos)
  write_all(stripped_name, stripped)

  tex.sprint("\\gdef\\markdownclass@baseclass{" .. tex_escape(dc.class) .. "}")
  tex.sprint("\\gdef\\markdownclass@baseoptions{" .. tex_escape(dc.options) .. "}")

  texio.write_nl(
    "markdown class: extracted base class `" ..
    dc.class ..
    "' with options `" ..
    dc.options ..
    "' from " ..
    preamble_name
  )
end

local function source_candidates_from_arg()
  local candidates = {}

  local options_with_separate_value = {
    ["-jobname"] = true,
    ["--jobname"] = true,
    ["-output-directory"] = true,
    ["--output-directory"] = true,
    ["-interaction"] = true,
    ["--interaction"] = true,
    ["-aux-directory"] = true,
    ["--aux-directory"] = true,
  }

  local skip_next = false

  for i = 1, #arg do
    local a = arg[i]

    if skip_next then
      skip_next = false
    elseif type(a) == "string" then
      if options_with_separate_value[a] then
        skip_next = true
      elseif a:sub(1, 1) ~= "-" then
        candidates[#candidates + 1] = a
      end
    end
  end

  return candidates
end

function markdownclass.find_source_file()
  for _, candidate in ipairs(source_candidates_from_arg()) do
    if readable(candidate) then
      return candidate
    end

    if not candidate:match("%.tex$") and readable(candidate .. ".tex") then
      return candidate .. ".tex"
    end
  end

  local fallback = tex.jobname .. ".tex"

  if readable(fallback) then
    return fallback
  end

  error("markdown class: cannot determine main source file")
end

local function strip_quotes(value)
  if not value then
    return nil
  end
  value = value:gsub("^%s+", ""):gsub("%s+$", "")
  return value:match('^"(.*)"$') or value:match("^'(.*)'$") or value
end

local function trim(value)
  return (value or ""):gsub("^%s+", ""):gsub("%s+$", "")
end

local function tex_escape_metadata(value)
  value = value or ""
  local replacements = {
    ["\\"] = "\\textbackslash{}",
    ["{"] = "\\{",
    ["}"] = "\\}",
    ["$"] = "\\$",
    ["&"] = "\\&",
    ["#"] = "\\#",
    ["_"] = "\\_",
    ["%"] = "\\%",
    ["~"] = "\\textasciitilde{}",
    ["^"] = "\\textasciicircum{}",
  }
  return (value:gsub("[\\{}$&#_%%~^]", replacements))
end

local function tex_url_arg(value)
  return (value or ""):gsub("[{}]", "")
end

local function split_lines(content)
  local lines = {}
  content = content:gsub("\r\n", "\n"):gsub("\r", "\n")
  for line in (content .. "\n"):gmatch("([^\n]*)\n") do
    table.insert(lines, line)
  end
  return lines
end

local function extract_front_matter(content)
  local lines = split_lines(content)
  local start_index = 1

  while lines[start_index] and trim(lines[start_index]) == "" do
    start_index = start_index + 1
  end

  local first_line = lines[start_index]
  if not first_line then
    return nil, content
  end

  local has_explicit_opener = trim(first_line) == "---"
  local has_implicit_opener = first_line:match("^title:%s*") ~= nil

  if not has_explicit_opener and not has_implicit_opener then
    return nil, content
  end

  local front_matter = {}
  local line_index = has_explicit_opener and (start_index + 1) or start_index
  local closing_index = nil

  while lines[line_index] do
    local line = lines[line_index]
    local stripped_line = trim(line)

    if stripped_line == "---" or stripped_line == "..." then
      closing_index = line_index
      break
    end

    if stripped_line == "" then
      closing_index = line_index
      break
    end

    table.insert(front_matter, line)
    line_index = line_index + 1
  end

  local body_start = closing_index and (closing_index + 1) or line_index
  local body = {}
  for index = body_start, #lines do
    table.insert(body, lines[index])
  end

  return table.concat(front_matter, "\n"), table.concat(body, "\n")
end

local function parse_metadata(front_matter)
  local metadata = {
    title = nil,
    date = nil,
    scalar_author = nil,
    authors = {},
    has_orcid = false,
    has_email = false,
    has_empty_date = false,
    formalization = {},
  }
  local current_author = nil
  local in_affiliations = false
  local in_formalization = false

  for line in (front_matter .. "\n"):gmatch("([^\n]*)\n") do
    if line:match("^formalization:%s*$") then
      in_formalization = true
      in_affiliations = false
    elseif in_formalization and line:match("^%s+") then
      local key, url = line:match("^%s+([a-z][a-z0-9%-]*):%s*(.-)%s*$")
      url = strip_quotes(url)
      if not key or not url or not url:match("^https?://")
          or url:find("[\\{}%%#%s]") then
        error("markdown class: invalid formalization root: " .. line)
      end
      if metadata.formalization[key] then
        error("markdown class: duplicate formalization root: " .. key)
      end
      metadata.formalization[key] = url
    else
      in_formalization = false
    end
    local title = line:match("^title:%s*(.*)$")
    local date = line:match("^date:%s*(.*)$")
    local scalar_author = line:match("^author:%s*(.+)$")
    local name = line:match("^%-%s+name:%s*(.*)$")
    local author_name = line:match("^%-%s+([^:]+):%s*$")
    local orcid = line:match("^%s+orcid:%s*(.*)$")
    local email = line:match("^%s+email:%s*(.*)$")
    local affiliation_start = line:match("^%s+affiliation:%s*$")
    local affiliation = line:match("^%s+%-%s+(.*)$")

    if title then
      metadata.title = strip_quotes(title)
      in_affiliations = false
    elseif date then
      metadata.date = strip_quotes(date)
      in_affiliations = false
    elseif scalar_author then
      metadata.scalar_author = strip_quotes(scalar_author)
      in_affiliations = false
    elseif name or author_name then
      current_author = {
        name = strip_quotes(name or author_name),
        orcid = nil,
        email = nil,
        affiliations = {},
      }
      table.insert(metadata.authors, current_author)
      in_affiliations = false
    elseif current_author and orcid then
      current_author.orcid = strip_quotes(orcid)
      metadata.has_orcid = metadata.has_orcid or current_author.orcid ~= ""
      in_affiliations = false
    elseif current_author and email then
      current_author.email = strip_quotes(email)
      metadata.has_email = metadata.has_email or current_author.email ~= ""
      in_affiliations = false
    elseif current_author and affiliation_start then
      in_affiliations = true
    elseif current_author and in_affiliations and affiliation then
      table.insert(current_author.affiliations, strip_quotes(affiliation))
    end
  end

  metadata.has_empty_date = metadata.date == nil or metadata.date == ""
  return metadata
end

local function emit_title(metadata)
  if metadata.title then
    tex.sprint("\\title{" .. tex_escape_metadata(metadata.title) .. "}")
  end
end

local function emit_scalar_author(metadata)
  if metadata.scalar_author and metadata.scalar_author ~= "" then
    tex.sprint("\\author{" .. tex_escape_metadata(metadata.scalar_author) .. "}")
  end
end

local function emit_structured_authors(metadata)
  local affiliation_ids = {}
  local affiliations = {}

  for _, author in ipairs(metadata.authors) do
    author.affiliation_ids = {}
    local author_affiliation_ids = {}
    for _, affiliation in ipairs(author.affiliations) do
      if not affiliation_ids[affiliation] then
        table.insert(affiliations, affiliation)
        affiliation_ids[affiliation] = #affiliations
      end
      local affiliation_id = affiliation_ids[affiliation]
      if not author_affiliation_ids[affiliation_id] then
        table.insert(author.affiliation_ids, affiliation_id)
        author_affiliation_ids[affiliation_id] = true
      end
    end
  end

  for _, author in ipairs(metadata.authors) do
    local affiliation_parts = {}
    for _, affiliation_id in ipairs(author.affiliation_ids) do
      table.insert(affiliation_parts, tostring(affiliation_id))
    end

    local has_affiliations = #affiliation_parts > 0
    local has_email = author.email and author.email ~= ""
    local part = tex_escape_metadata(author.name)
    if author.orcid and author.orcid ~= "" then
      part = part .. "\\raisebox{-0.45ex}{\\scriptsize\\orcidlink{" .. tex_url_arg(author.orcid) .. "}}"
      if has_affiliations then
        part = part .. "\\kern-0.4em"
      end
    end

    -- Authors without email can use authblk's standard
    -- \author[affiliations]{name} form. Authors with email still need custom
    -- inline affiliation superscripts because authblk has no per-author suffix
    -- hook. If/as soon as the authblk authors accept a pull request adding
    -- \authorsuffix[authorNumber]{email}, this custom branch can be removed and
    -- all authors can use the optional affiliation list.
    if has_email and has_affiliations then
      part = part .. "\\textsuperscript{" .. table.concat(affiliation_parts, ",") .. "}"
    end
    if has_email then
      part = part .. " ‹\\protect\\url{" .. tex_url_arg(author.email) .. "}›"
    end

    if has_email and has_affiliations then
      tex.sprint("\\author[ ]{" .. part .. "}")
    elseif has_email then
      tex.sprint("\\author[ ]{" .. part .. "}")
    elseif has_affiliations then
      tex.sprint("\\author[" .. table.concat(affiliation_parts, ",") .. "]{" .. part .. "}")
    else
      tex.sprint("\\author[ ]{" .. part .. "}")
    end
  end

  for index, affiliation in ipairs(affiliations) do
    tex.sprint("\\affil[" .. index .. "]{\\small " .. tex_escape_metadata(affiliation) .. "}")
  end
end

local function emit_date(metadata)
  if metadata.date and metadata.date ~= "" then
    tex.sprint("\\date{\\markdownclass@dateprefix " .. tex_escape_metadata(metadata.date) .. "}")
  else
    tex.sprint("\\predate{}\\date{}\\postdate{}")
  end
end

local function emit_metadata_requirements(metadata)
  if metadata.scalar_author or #metadata.authors <= 0 then
    tex.sprint("\\global\\markdownclassNeedsAuthblkfalse")
  else
    tex.sprint("\\global\\markdownclassNeedsAuthblktrue")
  end

  if metadata.has_empty_date then
    tex.sprint("\\global\\markdownclassNeedsTitlingtrue")
  else
    tex.sprint("\\global\\markdownclassNeedsTitlingfalse")
  end

  if metadata.has_orcid then
    tex.sprint("\\global\\markdownclassNeedsOrcidlinktrue")
  else
    tex.sprint("\\global\\markdownclassNeedsOrcidlinkfalse")
  end

  if metadata.has_email then
    tex.sprint("\\global\\markdownclassNeedsUrltrue")
  else
    tex.sprint("\\global\\markdownclassNeedsUrlfalse")
  end
end

local function emit_metadata(metadata)
  if next(metadata.formalization) then
    tex.sprint("\\RequirePackage{verified-badges}")
    local keys = {}
    for key in pairs(metadata.formalization) do table.insert(keys, key) end
    table.sort(keys)
    for _, key in ipairs(keys) do
      local assistant = key:match("^([a-z]+)")
      tex.sprint("\\DeclareFormalizationRoot[" .. assistant .. "]{" .. key ..
        "}{\\detokenize{" .. metadata.formalization[key] .. "}}")
    end
  end
  emit_title(metadata)

  if metadata.scalar_author then
    emit_scalar_author(metadata)
  else
    emit_structured_authors(metadata)
  end

  emit_date(metadata)
end

function markdownclass.prepare_body(tmp)
  local srcname = markdownclass.find_source_file()
  local s = read_all(srcname)
  local dc = parse_documentclass(s)

  local source_body = s:sub(dc.end_pos + 1)
  local front_matter, body = extract_front_matter(source_body)
  write_all(tmp, body)

  if front_matter then
    local metadata = parse_metadata(front_matter)
    markdownclass.metadata = metadata
    emit_metadata_requirements(metadata)
    tex.sprint("\\global\\markdownclassMetadataFoundtrue")
  else
    markdownclass.metadata = nil
    tex.sprint("\\global\\markdownclassMetadataFoundfalse")
    tex.sprint("\\global\\markdownclassNeedsAuthblkfalse")
    tex.sprint("\\global\\markdownclassNeedsTitlingfalse")
    tex.sprint("\\global\\markdownclassNeedsOrcidlinkfalse")
    tex.sprint("\\global\\markdownclassNeedsUrlfalse")
  end

  texio.write_nl(
    "markdown class: prepared Markdown body from " ..
    srcname ..
    " to " ..
    tmp
  )
end

function markdownclass.emit_metadata()
  if markdownclass.metadata then
    emit_metadata(markdownclass.metadata)
  end
end
\end{luacode*}

% Parse the external preamble before loading the real base class.
\directlua{
  markdownclass.parse_preamble(
    "\luaescapestring{\markdownclass@preamble}",
    "\luaescapestring{\markdownclass@strippedpreamble}"
  )
}

% Load the real base class declared inside preamble.tex.
\ifx\markdownclass@baseoptions\@empty
  \LoadClass{\markdownclass@baseclass}
\else
  \PassOptionsToClass{\markdownclass@baseoptions}{\markdownclass@baseclass}%
  \LoadClass{\markdownclass@baseclass}%
\fi

% Now input the preamble without its \documentclass line.
\InputIfFileExists{\markdownclass@strippedpreamble}{}{%
  \ClassError{markdown}
    {Could not input stripped preamble}
    {Expected file: \markdownclass@strippedpreamble}%
}
% A user preamble may legitimately end with \makeatother. Restore the class's
% internal-name catcode before reading the remaining class implementation.
\makeatletter

% Require the stripped preamble to have loaded the markdown package.
\@ifundefined{markdownInput}{%
  \ClassError{markdown}
    {The markdown package is not loaded}
    {Your preamble file must load it, for example:
     \string\usepackage{markdown}.}%
}{}

\newif\ifmarkdownclassMetadataFound
\newif\ifmarkdownclassNeedsAuthblk
\newif\ifmarkdownclassNeedsTitling
\newif\ifmarkdownclassNeedsOrcidlink
\newif\ifmarkdownclassNeedsUrl
\let\markdownclass@dateprefix\@empty
\newdimen\markdownclass@dateskip

% Extract metadata and the Markdown body from the real main source file.
\directlua{
  markdownclass.prepare_body(
    "\luaescapestring{\markdownclass@bodyfile}"
  )
}

\ifmarkdownclassNeedsAuthblk
  \@ifpackageloaded{authblk}{}{%
    \ClassError{markdown}
      {Structured author metadata requires the authblk package}
      {Load authblk in the preamble file, or use the scalar form:
       author: Author Name.}%
  }%
  \ifmarkdownclass@authorsonlines
    % Apply before author metadata is emitted: authblk stores separators in
    % its author list. Keep its affiliation and per-author metadata handling.
    \renewcommand\Authsep{\protect\\}%
    \renewcommand\Authand{\protect\\}%
    \renewcommand\Authands{\protect\\}%
    % Move the larger gap from before affiliations to before the date.
    % Preserve the total title spacing and the user's configured scale.
    \markdownclass@dateskip=.7\affilsep
    \affilsep=.3\affilsep
    \def\markdownclass@dateprefix{\par\vspace{\markdownclass@dateskip}}%
  \fi
\fi

\ifmarkdownclassNeedsTitling
  \@ifpackageloaded{titling}{}{%
    \ClassError{markdown}
      {Empty date metadata requires the titling package}
      {Load titling in the preamble file, because empty dates are emitted
       using \string\predate{} and \string\postdate{}.}%
  }%
\fi

\ifmarkdownclassNeedsOrcidlink
  \@ifpackageloaded{orcidlink}{}{%
    \ClassError{markdown}
      {ORCID metadata requires the orcidlink package}
      {Load orcidlink in the preamble file, or remove ORCID fields from
       the front matter.}%
  }%
\fi

\ifmarkdownclassNeedsUrl
  \@ifundefined{url}{%
    \ClassError{markdown}
      {Author email metadata requires \string\url}
      {Load hyperref or url in the preamble file, or remove email fields
       from the front matter.}%
  }{}%
\fi

\ifmarkdownclassMetadataFound
  \directlua{markdownclass.emit_metadata()}%
\fi

% This runs after \documentclass has finished loading the class, but before
% TeX reads the Markdown body from the main source as ordinary input.
\def\markdownclass@run{%
  \begin{document}%
  \ifmarkdownclassMetadataFound
    \maketitle
  \fi
  \markdownInput{\markdownclass@bodyfile}%
  \end{document}%
}

\g@addto@macro\@documentclasshook{\markdownclass@run}

\makeatother
