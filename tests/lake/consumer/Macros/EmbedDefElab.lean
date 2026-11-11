module

public meta import Lean.Elab.Command

/-! The same command by a command elaborator, which elaborates the quoted declaration. -/

public section

open Lean Elab Command

syntax (name := foreignEmbedDefElab) "embedDefElabForeign " ident str : command

@[command_elab foreignEmbedDefElab] meta def elabEmbedDefForeign : CommandElab := fun stx => do
  let n : TSyntax `ident := ⟨stx[1]⟩
  let p : TSyntax `str := ⟨stx[2]⟩
  elabCommand (← `(public def $n : String := include_str $p))

end
