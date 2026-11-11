import Lake

open Lake DSL

/-- The checking profile of the numerical certificates, from the option `certificates`. The
default `kernel` checks every `cega [fast]` certificate in the kernel and builds into `.lake/build`.
`fast` (alias `native`) evaluates them with compiled code, which additionally trusts Lean's
compiler, and builds into `.lake/build-fast`; select it with `lake build -R -Kcertificates=fast`.
With `-R`, any other value is an error of this configuration, and Lake stops before it builds
anything; without `-R`, Lake reuses the options it read last. A package that requires SymLean
forwards its own option with

    require SymLean ... with
      NameMap.empty.insert `certificates ((get_config? certificates).getD "kernel")
-/
def certificatesMode : String := run_io do
  match (get_config? certificates).getD "kernel" with
  | "kernel" => return "kernel"
  | "fast" | "native" => return "fast"
  | value =>
    throw <| .userError <|
      s!"unknown certificates profile '{value}': use kernel, fast or native, with lake -R"

/-- Lean arguments used throughout the library. Each compiler runs on one thread (`-j1`): Lake
already runs one compiler per hardware thread, and a compiler with several threads keeps the
memory of the kernel checks of several declarations at once, which roughly doubles the peak of a
certificate module. -/
def casLeanArgs : Array String := #[
  "-j1",
  "-Dpp.unicode.fun=true",
  "-DautoImplicit=false",
  "-DrelaxedAutoImplicit=false",
  "-Dweak.linter.mathlibStandardSet=true",
  "-DwarningAsError=true"
]

package SymLean where
  fixedToolchain := true
  version := v!"1.0.0"
  buildDir := if certificatesMode == "fast" then ".lake/build-fast" else ".lake/build"

-- FloatLib supplies executable floats and outward-rounded intervals.
require floatlib from git "https://github.com/lean-dojo/FloatLib.git" @ "main"

-- Hex (the Lean FRO's verified computer algebra, v0.10.0) is an optional dependency for the
-- routes of `CASHex/`, off by default. `lake -R -Khex=on update HexBerlekampZassenhausTheory
-- HexBareissTheory HexPrimalityTheory` fetches it, `lake -R -Khex=on build CASHex` builds the
-- routes, and `lake -R build` switches back; without `-Khex=on` Lake neither fetches nor builds
-- Hex.
meta if get_config? hex = some "on" then do
  require HexBerlekampZassenhausTheory from git
    "https://github.com/leanprover/hex-berlekamp-zassenhaus-theory.git" @ "v0.10.0"
  require HexBareissTheory from git
    "https://github.com/leanprover/hex-bareiss-theory.git" @ "v0.10.0"
  require HexPrimalityTheory from git
    "https://github.com/leanprover/hex-primality-theory.git" @ "v0.10.0"

-- The oracle library of `CASOracle/` is built on DSLean (taterowney/DSLean, CC-BY-4.0), which
-- translates between Lean and the oracles' languages and runs them. This is its Lean 4.35 port
-- with SymLean's fixes; it moves to upstream DSLean once those are merged there. Lake needs its
-- entry in lake-manifest.json: update with `lake -R -Koracle=on update DSLean`, since an update
-- without `-Koracle=on` drops the entry. Without `-Koracle=on` Lake neither fetches nor builds it.
meta if get_config? oracle = some "on" then
require DSLean from git "https://github.com/Robertboy18/DSLean.git" @
  "1b5f22ff70cd0810f52e6f01f56cdfdde0d9651a"

-- Mathlib stays last so its release pins govern the shared support packages.
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

/-! ## Embedded inputs

`include_str` reads a file while Lean elaborates the module, and `json_data%` reads its files
through `include_str`. A library whose `needs` list `` `@/‹library›:SymLean.embeddedInputs ``
rebuilds its modules when such a file changes, since Lake mixes the trace of a library's `needs`
into each of its modules.

The facet finds the files by a text search of every module that Lake builds as part of the
library: the modules of its globs, their local imports, and every module under the directory of
one of its roots. Each `include_str` in the text of a module, followed by whitespace and comments,
skipped as Lean skips them, and a string literal, ordinary or raw, names the file of that literal,
decoded as Lean decodes it and resolved against the module's directory. An occurrence in a comment
or a string only tracks one file more.

The check of `CAS.IncludeStr` makes the search find every file that Lean reads through
`include_str` in a module that loads it: it accepts an `include_str` only when the keyword and its
path, one string literal, are the text of the module's file at that place. The facet stops the
build at a module of the library

* whose text contains `include_str`, if only in a comment, but which does not load
  `CAS.IncludeStr` through its public imports (through any import, in a file outside the module
  system), so that each module that loads it, and so can expand its macros and notations, loads
  the check as well;
* that loads a module of the workspace whose text can produce `include_str` in another module, but
  does not load `CAS.IncludeStr`: a module whose text, outside comments, has `include_str` in a
  string literal, in a syntax quotation or in a command other than a declaration (`def`,
  `theorem`, `instance`, `structure` and the like);
* that loads a module of the workspace, itself included, whose text outside comments names the
  syntax kind of `include_str` or an elaborator of it (`includeStr`, `elabIncludeStr`,
  `checkIncludeStr`), as code that adds, replaces or removes such an elaborator does;
  `CAS.IncludeStr` is the exception.

The modules that Lean loads with a module are found by the rules of the module system: all imports
of the module itself, the public imports of the modules they import, transitively, all imports of
a module imported with `import all`, and every import, transitively, of a file outside the module
system.

With these rules, in a library that lists the facet, every file that Lean reads through
`include_str` while it elaborates a module of the library is tracked, or the build stops. What
stays outside is code that reads a file on purpose by other means: an elaborator or meta code
that reads it itself (with `IO.FS.readFile`, say), code that builds the syntax of `include_str` at
run time from pieces of text, so that neither `include_str` nor `includeStr` is in its text, or
that elaborates it under a file name and a file map that it sets up itself, and the macros and
elaborators of modules outside the workspace, that is, Lean's own, none of which produces
`include_str`.

Lake keeps one facet table for the whole workspace, in which a facet replaces any earlier one of
the same name, the facets of the packages that require SymLean included. Hence the facet's name
is qualified by the package's. -/

namespace EmbeddedInputs

/-- The module whose elaborator checks each `include_str`. -/
def checkModule : Lean.Name := `CAS.IncludeStr

/-- The byte at `i` of `s`, and `0` past its end. -/
def byteAt (s : ByteArray) (i : Nat) : UInt8 := if h : i < s.size then s[i] else 0

/-- Whether a comment starts at `i`: a line comment, or a block comment, doc comments included. -/
def commentAt (s : ByteArray) (i : Nat) : Bool :=
  (byteAt s i == 45 || byteAt s i == 47) && byteAt s (i + 1) == 45

/-- Where the comment at `i` ends: a line comment at the end of its line, a block comment after
the end that matches its opening, as Lean's `finishCommentBlock` reads it, nested and with the
character after the opening dash part of the opening; `none` for a block comment that does not
end. -/
def commentEnd (s : ByteArray) (i : Nat) : Option Nat := Id.run do
  if byteAt s i == 45 then
    let mut j := i + 2
    while j < s.size && byteAt s j != 10 do j := j + 1
    return some j
  let mut j := i + 3
  let mut depth := 1
  while depth > 0 do
    if j ≥ s.size then return none
    if byteAt s j == 45 && byteAt s (j + 1) == 47 then
      depth := depth - 1
      j := j + 2
    else if byteAt s j == 47 && byteAt s (j + 1) == 45 then
      depth := depth + 1
      j := j + 2
    else j := j + 1
  return some j

/-- Where the whitespace and comments from `i` end, as Lean's `whitespace` reads them, and doc
comments as well; `none` at a block comment that does not end. Lean refuses a tab or a carriage
return, which are skipped here: that only tracks more. -/
def skipGap (s : ByteArray) (i : Nat) : Option Nat := Id.run do
  let mut i := i
  repeat
    let c := byteAt s i
    if c == 32 || c == 10 || c == 9 || c == 13 then
      i := i + 1
    else if commentAt s i then
      let some j := commentEnd s i | return none
      i := j
    else break
  return some i

/-- Where the string literal at `i` ends, as Lean's lexer reads an ordinary literal (to the first
quote that no backslash escapes) or a raw one (`r`, some `#`, a quote, and to the first quote
followed by as many `#`); `none` if no literal starts at `i` or it does not end. -/
def literalEnd (s : ByteArray) (i : Nat) : Option Nat := Id.run do
  let mut j := i + 1
  if byteAt s i == 34 then
    while j < s.size do
      let c := byteAt s j
      if c == 34 then return some (j + 1)
      j := j + (if c == 92 then 2 else 1)
    return none
  if byteAt s i != 114 then return none
  let mut hashes := 0
  while byteAt s j == 35 do
    hashes := hashes + 1
    j := j + 1
  if byteAt s j != 34 then return none
  j := j + 1
  while j < s.size do
    if byteAt s j == 34 && (List.range hashes).all fun k ↦ byteAt s (j + 1 + k) == 35 then
      return some (j + 1 + hashes)
    j := j + 1
  return none

/-- Whether `word` occurs in `text`, by `String.splitOn`, which Lake runs as compiled code. -/
def occurs (word text : String) : Bool := (text.splitOn word).length > 1

/-- The paths that the text of a module gives to `include_str`: for each occurrence of the word
followed by whitespace and comments and a string literal, the literal decoded as Lean decodes it.
The text is read with its line endings normalized, as Lean reads it. The occurrences come from
`String.splitOn`; only the text after each one is read here. -/
def paths (source : String) : Array String := Id.run do
  let text := source.crlfToLf
  let s := text.toUTF8
  let word := "include_str"
  let mut found := #[]
  let mut stop := 0
  -- Each piece but the last ends where an occurrence of the word starts.
  for piece in (text.splitOn word).dropLast do
    stop := stop + piece.utf8ByteSize + word.utf8ByteSize
    if let some start := skipGap s stop then
      if let some literalStop := literalEnd s start then
        let literal := String.Pos.Raw.extract text ⟨start⟩ ⟨literalStop⟩
        if let some path := Lean.Syntax.decodeStrLit literal then found := found.push path
  return found

/-- The commands that declare a constant, whose `include_str` Lean elaborates in their module. -/
def declarationKeywords : List String :=
  ["def", "theorem", "lemma", "abbrev", "instance", "example", "opaque", "structure", "class",
    "inductive", "axiom"]

/-- The commands that define syntax, whose `include_str` Lean elaborates where the syntax is
used. A command that starts in the first column ends the one before, so these are needed only
for commands written further right. -/
def syntaxKeywords : List String :=
  ["notation", "notation3", "macro", "macro_rules", "syntax", "elab", "elab_rules", "infix",
    "infixl", "infixr", "prefix", "postfix", "binder_predicate"]

/-- The syntax kind of `include_str` and its elaborators, Lean's and the check's. -/
def elaboratorNames : List String := ["includeStr", "elabIncludeStr", "checkIncludeStr"]

/-- Whether the byte `c` continues an identifier: letters, digits, `_`, `'`, `!`, `?`, `.`, and
the bytes of a non-ASCII character. -/
def identByte (c : UInt8) : Bool :=
  (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || (48 ≤ c && c ≤ 57) || c == 95 || c == 39 ||
    c == 33 || c == 63 || c == 46 || 128 ≤ c

/-- What the text of a module does with `include_str`. -/
structure Uses where
  /-- The text contains `include_str`. -/
  mentions : Bool := false
  /-- Outside comments, the text has `include_str` in a string literal, in a syntax quotation or
  in a command other than a declaration, where a macro, a notation or an elaborator can take it
  to another module. -/
  produces : Bool := false
  /-- A word outside comments that names the syntax kind of `include_str` or an elaborator of
  it. -/
  names : Option String := none

/-- What `source`, the text of a module, does with `include_str`. The scan skips comments as
Lean does, reads string and character literals whole, and keeps the kind of the command that it
is in: a declaration from one of `declarationKeywords`, until a command starts in the first
column or one of `syntaxKeywords` comes, and the depth of parentheses in a syntax quotation
`` `( ``. Inside a quotation, as in a macro whose expansion is a `def`, `include_str` is produced
whatever the keywords before it, and a line in the first column does not end the command. Only
the texts that contain `include_str` or `ncludeStr` are scanned: `String.splitOn` decides that as
compiled code. -/
def uses (source : String) : Uses := Id.run do
  let text := source.crlfToLf
  let mentions := occurs "include_str" text
  unless mentions || occurs "ncludeStr" text do return {}
  let s := text.toUTF8
  let piece (i j : Nat) : String := String.Pos.Raw.extract text ⟨i⟩ ⟨j⟩
  let mut produces := false
  let mut names : Option String := none
  let mut declaration := false
  -- Depth of parentheses inside a syntax quotation; `0` outside one.
  let mut depth : Nat := 0
  let mut lineStart := true
  let mut i := 0
  while i < s.size do
    let c := byteAt s i
    if c == 10 then
      lineStart := true
      i := i + 1
      continue
    if c == 32 || c == 9 || c == 13 then
      lineStart := false
      i := i + 1
      continue
    if commentAt s i then
      let some j := commentEnd s i | break
      lineStart := false
      i := j
      continue
    if lineStart && depth == 0 then
      declaration := false
    lineStart := false
    let literal? := if c == 34 || c == 114 then literalEnd s i else none
    if let some j := literal? then
      let literal := piece i j
      produces := produces || occurs "include_str" literal
      names := names <|> elaboratorNames.find? (occurs · literal)
      i := j
    else if c == 39 then
      -- A character literal, such as `'"'` or `'\''`.
      let mut j := i + (if byteAt s (i + 1) == 92 then 3 else 2)
      while j < s.size && j < i + 12 && byteAt s j != 39 && byteAt s j != 10 do j := j + 1
      i := if byteAt s j == 39 then j + 1 else i + 1
    else if c == 96 && byteAt s (i + 1) == 40 then
      depth := depth + 1
      i := i + 2
    else if c == 40 && depth > 0 then
      depth := depth + 1
      i := i + 1
    else if c == 41 && depth > 0 then
      depth := depth - 1
      i := i + 1
    else if identByte c && c != 39 && c != 46 then
      let mut j := i + 1
      while j < s.size && identByte (byteAt s j) do j := j + 1
      let word := piece i j
      names := names <|> elaboratorNames.find? (occurs · word)
      if occurs "include_str" word then
        produces := produces || !declaration || depth > 0
      else if declarationKeywords.contains word then
        declaration := true
      else if syntaxKeywords.contains word then
        declaration := false
      i := j
    else i := i + 1
  return { mentions, produces, names }

/-- Which imports of a module Lean follows when it loads the module for the one it elaborates:
all of them, transitively, when that module is outside the module system (`every`); all imports
of this module, when it is the module being elaborated or loaded with `import all` (`all`); its
`public` imports only, otherwise (`exported`). -/
inductive Reach where
  | every
  | all
  | exported
  deriving BEq, Hashable

/-- What Lean loads with a module: whether `checkModule`, the first module that can produce
`include_str` in another one, and the first module other than `checkModule` that names the syntax
kind or an elaborator of `include_str`, with the name. -/
structure Loaded where
  check : Bool := false
  producer : Option Lean.Name := none
  naming : Option (Lean.Name × String) := none

/-- The answers so far: for each module and `Reach`, what Lean loads with it, and for each module,
what its text does with `include_str`. -/
structure Tables where
  loaded : Std.HashMap (Lean.Name × Reach) Loaded := {}
  uses : Std.HashMap Lean.Name Uses := {}

/-- What the text of `mod` does with `include_str`, read once. -/
def usesOf (mod : Module) : StateT Tables FetchM Uses := do
  if let some known := (← get).uses[mod.name]? then return known
  let found := uses (← IO.FS.readFile mod.leanFile)
  modify fun tables ↦ { tables with uses := tables.uses.insert mod.name found }
  return found

/-- What Lean loads with `mod`, which it reaches as `reach` says: `mod` itself and the modules
of the workspace that it loads through the imports of `mod`. -/
partial def loaded (mod : Module) (reach : Reach) : StateT Tables FetchM Loaded := do
  if let some known := (← get).loaded[(mod.name, reach)]? then return known
  let own ← usesOf mod
  let isCheck := mod.name == checkModule
  let mut result : Loaded := {
    check := isCheck
    producer := if own.produces then some mod.name else none
    naming := if isCheck then none else own.names.map (mod.name, ·) }
  let followed := (← (← mod.input.fetch).await).imports.filterMap fun imp ↦
    match reach, imp.module? with
    | .every, some imported => some (imported, Reach.every)
    | .all, some imported => some (imported, if imp.importAll then .all else .exported)
    | .exported, some imported => if imp.isExported then some (imported, .exported) else none
    | _, none => none
  for (imported, next) in followed do
    let more ← loaded imported next
    result := {
      check := result.check || more.check
      producer := result.producer <|> more.producer
      naming := result.naming <|> more.naming }
  modify fun tables ↦ { tables with loaded := tables.loaded.insert (mod.name, reach) result }
  return result

/-- The modules that Lake builds as part of `lib`: those of its globs and their local imports
(`lib.modules`), and every module under the directory of one of its roots, which Lake treats as
local to the library (`LeanLibConfig.isLocalModule`). -/
def localModules (lib : LeanLib) : FetchM (Array Module) := do
  let mut modules := (← (← lib.modules.fetch).await)
  let seen ← IO.mkRef (Std.HashSet.ofList (modules.map (·.name)).toList)
  let found ← IO.mkRef (#[] : Array Lean.Name)
  let add (name : Lean.Name) : IO Unit := do
    unless (← seen.get).contains name do
      seen.modify (·.insert name)
      found.modify (·.push name)
  for root in lib.roots do
    if ← (Lean.modToFilePath lib.srcDir root "lean").pathExists then add root
    let directory := Lean.modToFilePath lib.srcDir root ""
    if ← directory.isDir then
      Lean.forEachModuleInDir (m := IO) directory fun name ↦ add (root ++ name)
  for name in ← found.get do
    modules := modules.push { lib, name }
  return modules

end EmbeddedInputs

/-- The data files that the modules of a library embed with `include_str`, each resolved against
its module's directory, as one job whose trace mixes theirs. A library that lists this facet in
its `needs` rebuilds its modules when one of the files changes, and stops at a module that breaks
one of the rules of the doc block above. A missing file is traced as missing; Lean reports it when
it elaborates the module. -/
library_facet SymLean.embeddedInputs (lib : LeanLib) : Array System.FilePath := do
  let check := EmbeddedInputs.checkModule
  let mut tables : EmbeddedInputs.Tables := {}
  let mut inputs : Array System.FilePath := #[]
  let mut jobs := #[]
  for mod in ← EmbeddedInputs.localModules lib do
    let file := mod.leanFile
    let isModule := (← (← mod.input.fetch).await).header.isModule
    let (here, next) ← (EmbeddedInputs.loaded mod (if isModule then .all else .every)).run tables
    let (own, next) ← (EmbeddedInputs.usesOf mod).run next
    tables := next
    if let some (other, word) := here.naming then
      let which := if other == mod.name then "names" else s!"loads {other}, which names"
      error s!"{file}: this module {which} {word}, the syntax kind or an elaborator of \
        include_str, as code that adds, replaces or removes an elaborator of include_str does; \
        such code could read a file that the build does not track, so a library that lists \
        SymLean.embeddedInputs must not have or load it"
    if own.mentions then
      let reach : EmbeddedInputs.Reach := if isModule then .exported else .every
      let (exported, next) ← (EmbeddedInputs.loaded mod reach).run tables
      tables := next
      unless exported.check do
        if isModule then
          error s!"{file}: this module contains include_str but does not load {check} through \
            its public imports; {check} checks that the build can track each include_str, here \
            and in each module that loads this one and so can expand its macros and notations: \
            add `public import {check}`"
        else
          error s!"{file}: this module contains include_str but does not load {check}, which \
            checks that the build can track each include_str; add `import {check}`"
    if let some producer := here.producer then
      unless here.check do
        error s!"{file}: this module loads {producer}, whose text has include_str in a string, \
          a syntax quotation or a command other than a declaration, so that its macros, \
          notations or elaborators can produce include_str here; add `import {check}`, which \
          refuses such an include_str"
    if own.mentions then
      for path in EmbeddedInputs.paths (← IO.FS.readFile file) do
        let path := file.parent.getD "." / path
        unless inputs.contains path do
          inputs := inputs.push path
          let isFile := (← path.pathExists) && !(← path.isDir)
          jobs := jobs.push (← if isFile then inputBinFile path else pure (Job.pure path))
  return Job.collectArray jobs s!"{lib.name}:SymLean.embeddedInputs"

@[default_target]
lean_lib CAS where
  globs := #[.andSubmodules `CAS]
  needs := #[`@/CAS:SymLean.embeddedInputs]
  moreLeanArgs := casLeanArgs ++
    #[if certificatesMode == "fast" then "-Dweak.cega.nativeCertificates=true"
      else "-Dweak.cega.nativeCertificates=false"]

-- The optional routes through Hex (`CASHex/`), built only with `lake -R -Khex=on build CASHex`.
-- `CAS` never imports them.
meta if get_config? hex = some "on" then
lean_lib CASHex where
  globs := #[.submodules `CASHex]
  needs := #[`@/CASHex:SymLean.embeddedInputs]
  moreLeanArgs := casLeanArgs

-- The optional oracle library (`CASOracle/`), built only with
-- `lake -R -Koracle=on build CASOracle`. Its files are ordinary files rather than `module`s,
-- because DSLean's are. `CAS` never imports
-- them, so the default build needs neither DSLean nor any external program.
meta if get_config? oracle = some "on" then
lean_lib CASOracle where
  globs := #[.submodules `CASOracle]
  needs := #[`@/CASOracle:SymLean.embeddedInputs]
  allowNonModules := true
  moreLeanArgs := casLeanArgs
