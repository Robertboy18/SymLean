/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Arsinh
import DSLean.Command

/-!
# The languages of the oracles, declared with DSLean

Each oracle's syntax for real expressions is a DSLean `external` declaration, one per direction:

* `sympyOut` writes a real term as SymPy source, which the Python programs read with SymPy's
  `parse_expr` (so `1 / 3` stays a rational); FLINT and Sage read it the same way;
* `sympyIn` reads SymPy's `str` of an answer, which is also how the answers of PARI, FLINT and
  Sage are printed;
* `gpOut` writes PARI/GP's syntax;
* `maximaOut` and `maximaIn` write and read Maxima's;
* Gappa's is DSLean's own `Gappa_input`.

The writing grammars parenthesize every operation, since DSLean concatenates a pattern's text
around its blanks; priorities make powers and functions match before the operations they unfold
to. The reading grammars follow the programs' precedences. Answers elaborate as real terms over
the request's variables only; `CASOracle.Translate` reflects them into checked expressions, and
nothing read here is trusted. The tokens of these grammars (`E`, `pi`, `%e`) are keywords in this
file only, so it holds nothing else.

The grammar language, the translations `toExternal'` and `fromExternal'` that run a grammar,
and `Gappa_input` come from DSLean. CASOracle uses DSLean as a Lake package and copies none of
its code. The revision we pin is DSLean's port to Lean 4.35.0 (`CASOracle.Oracle` lists its
changes), and the grammars below rely on two of them: the reading grammars on operand
precedences that follow the `precedence` option, the writing grammars on pattern priorities that
hold in `toExternal'`.

## References

* taterowney, *DSLean: A Bi-directional Interface Between Lean 4 and External Languages*,
  <https://github.com/taterowney/DSLean>, licensed under CC BY 4.0,
  <https://creativecommons.org/licenses/by/4.0/>. NOTICE gives the revision we pin.
-/

-- DSLean finds the blanks of a pattern through auto-bound implicits.
set_option autoImplicit true
set_option linter.unusedVariables false

external sympyOut where
  "(" x "**" y ")" <== (x : ℝ) ^ (y : ℕ) ; (priority := 30)
  "(" x "**" y ")" <== (x : ℝ) ^ (y : ℝ) ; (priority := 30)
  "sin(" x ")" <== Real.sin x ; (priority := 20)
  "cos(" x ")" <== Real.cos x ; (priority := 20)
  "atan(" x ")" <== Real.arctan x ; (priority := 20)
  "asin(" x ")" <== Real.arcsin x ; (priority := 20)
  "acos(" x ")" <== Real.arccos x ; (priority := 20)
  "exp(" x ")" <== Real.exp x ; (priority := 20)
  "log(" x ")" <== Real.log x ; (priority := 20)
  "sqrt(" x ")" <== Real.sqrt x ; (priority := 20)
  "pi" <== Real.pi ; (priority := 20)
  "(-" x ")" <== -(x : ℝ) ; (priority := 10)
  "(" x "-" y ")" <== (x : ℝ) - y ; (priority := 5)
  "(" x "/" y ")" <== (x : ℝ) / y ; (priority := 5)
  "(" x "+" y ")" <== (x : ℝ) + y
  "(" x "*" y ")" <== (x : ℝ) * y

external sympyIn where
  x "+" y ==> (x : ℝ) + (y : ℝ) ; (precedence := 0)
  x "-" y ==> (x : ℝ) - (y : ℝ) ; (precedence := 0)
  x "*" y ==> (x : ℝ) * (y : ℝ) ; (precedence := 1)
  x "/" y ==> (x : ℝ) / (y : ℝ) ; (precedence := 1)
  "-" x ==> -(x : ℝ) ; (precedence := 2)
  x "**" y ==> (x : ℝ) ^ (y : ℝ) ; (precedence := 3) +rightAssociative
  "(" x ")" ==> x
  "E" ==> Real.exp 1
  "pi" ==> Real.pi
  "sin(" x ")" ==> Real.sin x
  "cos(" x ")" ==> Real.cos x
  "tan(" x ")" ==> Real.tan x
  "atan(" x ")" ==> Real.arctan x
  "asin(" x ")" ==> Real.arcsin x
  "acos(" x ")" ==> Real.arccos x
  "exp(" x ")" ==> Real.exp x
  "log(" x ")" ==> Real.log x
  "sqrt(" x ")" ==> Real.sqrt x
  "Abs(" x ")" ==> |(x : ℝ)|
  "sinh(" x ")" ==> Real.sinh x
  "cosh(" x ")" ==> Real.cosh x
  "tanh(" x ")" ==> Real.tanh x

external gpOut where
  "(" x "^" y ")" <== (x : ℝ) ^ (y : ℕ) ; (priority := 30)
  "(" x "^" y ")" <== (x : ℝ) ^ (y : ℝ) ; (priority := 30)
  "sin(" x ")" <== Real.sin x ; (priority := 20)
  "cos(" x ")" <== Real.cos x ; (priority := 20)
  "atan(" x ")" <== Real.arctan x ; (priority := 20)
  "asin(" x ")" <== Real.arcsin x ; (priority := 20)
  "acos(" x ")" <== Real.arccos x ; (priority := 20)
  "exp(" x ")" <== Real.exp x ; (priority := 20)
  "log(" x ")" <== Real.log x ; (priority := 20)
  "sqrt(" x ")" <== Real.sqrt x ; (priority := 20)
  "Pi" <== Real.pi ; (priority := 20)
  "(-" x ")" <== -(x : ℝ) ; (priority := 10)
  "(" x "-" y ")" <== (x : ℝ) - y ; (priority := 5)
  "(" x "/" y ")" <== (x : ℝ) / y ; (priority := 5)
  "(" x "+" y ")" <== (x : ℝ) + y
  "(" x "*" y ")" <== (x : ℝ) * y

external maximaOut where
  "(" x "^" y ")" <== (x : ℝ) ^ (y : ℕ) ; (priority := 30)
  "(" x "^" y ")" <== (x : ℝ) ^ (y : ℝ) ; (priority := 30)
  "sin(" x ")" <== Real.sin x ; (priority := 20)
  "cos(" x ")" <== Real.cos x ; (priority := 20)
  "atan(" x ")" <== Real.arctan x ; (priority := 20)
  "asin(" x ")" <== Real.arcsin x ; (priority := 20)
  "acos(" x ")" <== Real.arccos x ; (priority := 20)
  "exp(" x ")" <== Real.exp x ; (priority := 20)
  "log(" x ")" <== Real.log x ; (priority := 20)
  "sqrt(" x ")" <== Real.sqrt x ; (priority := 20)
  "%pi" <== Real.pi ; (priority := 20)
  "(-" x ")" <== -(x : ℝ) ; (priority := 10)
  "(" x "-" y ")" <== (x : ℝ) - y ; (priority := 5)
  "(" x "/" y ")" <== (x : ℝ) / y ; (priority := 5)
  "(" x "+" y ")" <== (x : ℝ) + y
  "(" x "*" y ")" <== (x : ℝ) * y

external maximaIn where
  x "+" y ==> (x : ℝ) + (y : ℝ) ; (precedence := 0)
  x "-" y ==> (x : ℝ) - (y : ℝ) ; (precedence := 0)
  x "*" y ==> (x : ℝ) * (y : ℝ) ; (precedence := 1)
  x "/" y ==> (x : ℝ) / (y : ℝ) ; (precedence := 1)
  "-" x ==> -(x : ℝ) ; (precedence := 2)
  x "^" y ==> (x : ℝ) ^ (y : ℝ) ; (precedence := 3) +rightAssociative
  "(" x ")" ==> x
  "%e" ==> Real.exp 1
  "%pi" ==> Real.pi
  "sin(" x ")" ==> Real.sin x
  "cos(" x ")" ==> Real.cos x
  "tan(" x ")" ==> Real.tan x
  "atan(" x ")" ==> Real.arctan x
  "asin(" x ")" ==> Real.arcsin x
  "acos(" x ")" ==> Real.arccos x
  "exp(" x ")" ==> Real.exp x
  "log(" x ")" ==> Real.log x
  "sqrt(" x ")" ==> Real.sqrt x
  "abs(" x ")" ==> |(x : ℝ)|
  "sinh(" x ")" ==> Real.sinh x
  "cosh(" x ")" ==> Real.cosh x
  "tanh(" x ")" ==> Real.tanh x
