module

/-! A command macro whose expansion is a declaration that uses `include_str`, in a library that
does not list the facet: the `def` inside the quotation must not make this a non-producer. -/

public section

macro "embedDefForeign " n:ident p:str : command => `(public def $n : String := include_str $p)

end
