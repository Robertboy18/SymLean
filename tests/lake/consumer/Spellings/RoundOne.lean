module

public import Lean.Elab.Command
public meta import Lean.Elab.Term
import Batteries.Tactic.Alias
public import CAS.IncludeStr

/-! Paths after notations, macros, custom commands and other syntax of the module, all tracked. -/

/-- A notation, then a hash command that embeds a file. -/
notation "two" => 2
#check ((include_str "data/after-notation.txt").length + two)

/-- A macro, then `open … in` and a hash command. -/
macro "five" : term => `(5)
open Lean in
#check include_str "data/after-macro.txt"

/-- An infix operator, then `set_option … in` and a hash command. -/
infixl:65 " +++ " => HAppend.hAppend
set_option pp.all true in
#check ((include_str "data/after-infix.txt") +++ "")

/-- A command of this module's own syntax, whose term is the `include_str` written here. -/
syntax "defstr " ident " := " term : command
macro_rules | `(defstr $n := $t) => `(def $n : String := $t)
defstr customCommand := include_str "data/custom-command.txt"

/-- A `do` block whose next line follows the path. -/
public def doNext : IO Unit := do
  let s := include_str "data/do-next.txt"
  IO.println s

/-- A definition and its alias. -/
public def aliased : String := include_str "data/alias.txt"
alias aliasedAgain := aliased

/-- Fields named like commands. -/
public structure Fields where
  «syntax» : Nat
  «prefix» : Nat

public def fields (s : Fields) : Nat :=
  (s).prefix + (s).syntax + (include_str "data/fields.txt").length

open Lean in
/-- An error message with a lone quote in a hole, then a string that mentions the keyword. -/
public def oops (stx : Syntax) : Elab.Command.CommandElabM Unit :=
  throwErrorAt stx "got {'"'} here"
public def mentioned : String := "include_str \"s0.txt\""
public def afterDesync : String := include_str "data/after-desync.txt"

open Lean in
/-- An `elab` whose body embeds a file, read where the command is elaborated. -/
elab "embedded!" : term => return mkStrLit (include_str "data/elab.txt")
