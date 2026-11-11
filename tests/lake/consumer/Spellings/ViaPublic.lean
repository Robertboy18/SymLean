module

public import Spellings.Public

/-- The check comes through the public import of `Spellings.Public`, and this module passes it on
through its own public import. -/
public def viaPublic : String := include_str "data/via-public.txt"
