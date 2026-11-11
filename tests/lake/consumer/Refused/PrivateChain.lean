module

import Refused.Private

/-- The check of `Refused.Private` is not loaded here: Lean does not follow its private import. -/
public def privateChain : String := include_str "data.txt"
