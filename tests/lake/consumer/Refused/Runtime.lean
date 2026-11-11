module

public import CAS.IncludeStr
meta import Lean.Elab.Command

/-! A command parsed from a string and elaborated with that string as its file map, which the check
refuses: the text is not the module's file, which the facet searches. -/

open Lean Elab Command in
run_cmd do
  let text := "public def runtime : String := include_str \"data.txt\""
  let stx ← match Parser.runParserCategory (← getEnv) `command text (← getFileName) with
    | .ok stx => pure stx
    | .error e => throwError e
  withReader (fun ctx ↦ { ctx with fileMap := FileMap.ofString text }) (elabCommand stx)
