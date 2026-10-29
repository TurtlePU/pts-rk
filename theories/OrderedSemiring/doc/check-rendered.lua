-- A successful TeX run does not imply that Markdown retained raw mathematics.
-- This note uses percent macros in prose; literal TeX listings are separate
-- .verbatim files, not candidates for the checks below.
local lfs = require("lfs")
local directory = assert(arg[1], "usage: texlua check-rendered.lua CACHE-DIR")
local checked, bad = 0, false
for name in lfs.dir(directory) do
  if name:match("%.md%.tex$") then
    checked = checked + 1
    local path = directory .. "/" .. name
    local file = assert(io.open(path, "rb"))
    local text = file:read("*a")
    file:close()
    for line in (text .. "\n"):gmatch("([^\n]*)\n") do
      if line:find("\\markdownRendererBackslash{}%a")
          or line:find("\\markdownRendererDollar", 1, true) then
        print(path .. ": escaped TeX command or math delimiter: " .. line)
        bad = true
      end
      if line:find(":::", 1, true) then
        print(path .. ": literal environment fence: " .. line)
        bad = true
      end
    end
    if text:find("\\begin{mathpar}%s*\\end{mathpar}") then
      print(path .. ": empty mathpar block; inspect the source boundary")
      bad = true
    end
  end
end
assert(checked > 0, "no rendered Markdown cache was found")
if bad then os.exit(1) end
print("Checked " .. checked .. " rendered Markdown file(s): no escaped math or empty mathpar blocks.")
