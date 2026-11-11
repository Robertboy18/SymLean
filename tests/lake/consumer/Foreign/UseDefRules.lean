module

import Macros.EmbedDefRules

/-! The `macro_rules` command of another library, whose expansion reads a file here: the facet
refuses this module, which does not load the check. -/

embedDefRulesForeign foreignDefRules "data.txt"
