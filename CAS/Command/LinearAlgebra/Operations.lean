/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.LinearAlgebra.Basic
public meta import CAS.Tactic.RouteRegistry

/-!
# Matrix arithmetic: `#cas [det]`, `[inverse]`, `[transpose]`, `[trace]`, `[matrixPower]`, `[dot]`

For matrices with rational entries, as Mathematica's `Det`, `Inverse`, `Transpose`, `Tr`,
`MatrixPower` and `Dot`. The statements are about Mathlib's `Matrix (Fin m) (Fin n) ℚ`:

* `det`: `A.det = d`, computed and proved by Mathlib's `norm_det` (with `-Khex=on`,
  `CASHex.LinearAlgebra` registers a backend that computes it with Hex's Bareiss elimination
  instead);
* `inverse`: `A⁻¹ = B` from `B * A = 1` (`Matrix.inv_eq_left_inv`), the product checked by kernel
  evaluation; a singular matrix is reported as such with `A.det = 0`, since Mathlib's total
  inverse of a singular matrix is `0`;
* `transpose`, `trace`, `matrixPower k` and `dot`: `Aᵀ = B`, `A.trace = t`, `A ^ k = B` and
  `A * B = C`, each decided by kernel evaluation (`decide +kernel`).

## Implementation notes

SymLean computes no determinant value itself. Mathlib's `norm_det` evaluates the determinant of
the literal (`detByNormDet`) and proves it, and with `-Khex=on` the `@[cas_route det]` backend of
`CASHex/LinearAlgebra.lean` answers first. The inverse is the matrix of row operations of
`rowReduce`, which `QMatrix.inverse?` of `CAS/Command/LinearAlgebra/Basic.lean` returns when the
reduced form is the identity; otherwise `norm_det` proves that the determinant is `0`. The other
results are computed in meta code (the power by `k` multiplications, for `k ≤ 1000`), and the
kernel evaluates the equation between the literals.
-/

public meta section

namespace CAS.Command.LinearAlgebra

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Command.Algebra (natTerm ratText proveStatement)

/-- Run `#cas [det] A`. -/
def logDet (ref : Syntax) (input : Syntax) : CommandElabM Unit := do
  let A ← parseQMatrix input
  unless A.rows = A.cols do throwErrorAt input "det: the matrix must be square"
  let (proposition, proof, d) : Lean.Expr × Lean.Expr × ℚ ← liftTermElabM do
    let At ← matrixTerm A A.rows A.cols
    let some d ← detByNormDet At
      | throwError "det: Mathlib's norm_det did not reduce the determinant to a number"
    let (a, b) ← proveStatement "det" (← `(Matrix.det $At = $(← ratTerm d))) (← detTactic)
    pure (a, b, d)
  logReport ref {
    domain := matrixDomain A
    input := A.text
    inputType := "matrix"
    output := ratText d
    outputType := "determinant"
  } #[← evidence "det" "Determinant" proposition proof]

/-- Run `#cas [inverse] A`. -/
def logInverse (ref : Syntax) (input : Syntax) : CommandElabM Unit := do
  let A ← parseQMatrix input
  unless A.rows = A.cols do throwErrorAt input "inverse: the matrix must be square"
  let n := A.rows
  match A.inverse? with
  | some B =>
      let (proposition, proof) ← liftTermElabM do
        let At ← matrixTerm A n n
        let Bt ← matrixTerm B n n
        proveStatement "inverse" (← `($At⁻¹ = $Bt))
          (← `(tactic| exact Matrix.inv_eq_left_inv (by decide +kernel)))
      logReport ref {
        domain := matrixDomain A
        input := A.text
        inputType := "matrix"
        output := B.text
        outputType := "inverse"
      } #[← evidence "inverse" "Inverse from the product B * A = 1" proposition proof]
  | none =>
      let (proposition, proof) ← liftTermElabM do
        let At ← matrixTerm A n n
        proveStatement "inverse" (← `(Matrix.det $At = 0)) (← detTactic)
      logReport ref {
        domain := matrixDomain A
        input := A.text
        inputType := "matrix"
        output := "the matrix is singular (determinant 0); Mathlib's A⁻¹ is 0"
        outputType := "no inverse"
      } #[← evidence "inverse" "The determinant vanishes" proposition proof]

/-- What a decided matrix computation reports. -/
inductive Arithmetic where
  | transpose
  | trace
  | power (k : Nat)

/-- Run `#cas [transpose] A`, `[trace] A` or `[matrixPower k] A`. -/
def logArithmetic (ref : Syntax) (operation : Arithmetic) (input : Syntax) :
    CommandElabM Unit := do
  let A ← parseQMatrix input
  let name := match operation with
    | .transpose => "transpose" | .trace => "trace" | .power k => s!"matrixPower {k}"
  match operation with
  | .transpose => pure ()
  | _ => unless A.rows = A.cols do throwErrorAt input "{name}: the matrix must be square"
  if let .power k := operation then
    if k > 1000 then
      throwErrorAt input "{name}: the power is decided by kernel evaluation, up to exponent 1000"
  let (proposition, proof, shown) : Lean.Expr × Lean.Expr × String ← liftTermElabM do
    let At ← matrixTerm A A.rows A.cols
    match operation with
    | .transpose =>
        let B := A.transpose
        let Bt ← matrixTerm B B.rows B.cols
        let (a, b) ← proveStatement name (← `(Matrix.transpose $At = $Bt)) (← kernelDecide)
        pure (a, b, B.text)
    | .trace =>
        let t := A.trace
        let (a, b) ← proveStatement name (← `(Matrix.trace $At = $(← ratTerm t))) (← kernelDecide)
        pure (a, b, ratText t)
    | .power k =>
        let B := (List.range k).foldl (fun P _ ↦ P.mul A) (QMatrix.identity A.rows)
        let (a, b) ← proveStatement name
          (← `($At ^ $(natTerm k) = $(← matrixTerm B A.rows A.cols))) (← kernelDecide)
        pure (a, b, B.text)
  logReport ref {
    domain := matrixDomain A
    input := A.text
    inputType := "matrix"
    output := shown
    outputType := match operation with
      | .transpose => "transpose" | .trace => "trace" | .power _ => "power"
  } #[← evidence name "Decided by kernel evaluation" proposition proof]

/-- Run `#cas [dot] (A, B)`: the product of two matrices, or of a matrix and a vector. -/
def logDot (ref : Syntax) (left right : Syntax) : CommandElabM Unit := do
  let A ← parseQMatrix left
  let vector? : Option (Array ℚ) ← try pure (some (← parseQVector right)) catch _ => pure none
  let (proposition, proof, shown, input) : Lean.Expr × Lean.Expr × String × String ←
    match vector? with
    | some v =>
        unless A.cols = v.size do throwErrorAt ref "dot: the sizes do not match"
        let w := A.mulVec v
        let (a, b) ← liftTermElabM do
          proveStatement "dot"
            (← `(Matrix.mulVec $(← matrixTerm A A.rows A.cols) $(← vectorTerm v) =
              $(← vectorTerm w)))
            (← kernelDecide)
        pure (a, b, vectorText w, s!"{A.text} . {vectorText v}")
    | none =>
        let B ← parseQMatrix right
        unless A.cols = B.rows do throwErrorAt ref "dot: the sizes do not match"
        let C := A.mul B
        let (a, b) ← liftTermElabM do
          proveStatement "dot"
            (← `($(← matrixTerm A A.rows A.cols) * $(← matrixTerm B B.rows B.cols) =
              $(← matrixTerm C A.rows B.cols)))
            (← kernelDecide)
        pure (a, b, C.text, s!"{A.text} . {B.text}")
  logReport ref {
    domain := matrixDomain A
    input := input
    inputType := "product"
    output := shown
    outputType := "product"
  } #[← evidence "dot" "Decided by kernel evaluation" proposition proof]

end CAS.Command.LinearAlgebra

namespace CAS.Command

open Lean Elab Command

/-- `#cas [det] A` computes the determinant of a square matrix `A` with rational entries and proves
it.

## Theorem
The report proves `A.det = d` for Mathlib's determinant of `A : Matrix (Fin n) (Fin n) ℚ`, with
Mathlib's simproc `norm_det`, which evaluates the determinant of a matrix literal.

## Conditions and limits
`A` is a square matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]`, and each
entry is a closed rational expression such as `-3/2`, `0.25` or `1/10^15`.

## Options
None.

## Examples
```lean
#cas [det] !![1, 2, 3; 4, 5, 6; 7, 8, 10]
```
```output
Output (determinant): -3
```
```lean
#cas [det] !![2, -1, 0, 0, 1; -1, 2, -1, 0, 0; 0, -1, 2, -1, 0; 0, 0, -1, 2, -1; 1, 0, 0, -1, 2]
```
```output
Output (determinant): 4
```
```lean
#cas [det] !![1/2, 1; 3, 4]
```
```output
Output (determinant): -1
```

## In a proof
```lean
theorem det_three : Matrix.det !![(1 : ℚ), 2, 3; 4, 5, 6; 7, 8, 10] = -3 := by
  cas
```

## See also
Mathematica `Det`, SymPy `Matrix.det`, Hex `Hex.norm_det` (through `CASHex.LinearAlgebra`, which
computes the determinant by fraction-free Bareiss elimination and prints
`Output (determinant (Hex's Bareiss certificate))`). The modes `inverse`,
`characteristicPolynomial` and `matrixRank`, and Mathlib's tactic `eval_det`.

## Possible issues
```lean
#cas [det] !![1, 2, 3; 4, 5, 6]
```
```output
det: the matrix must be square
```
The determinant is defined for square matrices only.
```lean
#cas [det] !![x, 1; 1, 1]
```
```output
expected a rational number, such as -3/2, 0.25 or 1/10^15
```
The entries are rational numbers. In a proof, `cas` evaluates the determinant of a matrix literal
with symbolic entries, and so does Mathlib's `eval_det` followed by `ring`.
-/
syntax (name := casDetCommand) "#cas" "[" &"det" "]" term : command

/-- `#cas [inverse] A` computes the inverse of a square matrix `A` with rational entries and proves
it, or proves that `A` is singular.

## Theorem
For an invertible `A` the report proves `A⁻¹ = B` for Mathlib's inverse over `ℚ`, from the
product `B * A = 1`, which the kernel evaluates (`Matrix.inv_eq_left_inv`). For a singular `A` it
prints `Output (no inverse)` and proves `A.det = 0`; Mathlib's `A⁻¹` is then the zero matrix.

## Conditions and limits
`A` is a square matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]`, and each
entry is a closed rational expression such as `-3/2`, `0.25` or `1/10^15`.

## Options
None.

## Examples
```lean
#cas [inverse] !![1, 2; 3, 4]
```
```output
Output (inverse): !![-2, 1; 3/2, -1/2]
```
```lean
#cas [inverse] !![1, 2, 3; 0, 1, 4; 5, 6, 0]
```
```output
Output (inverse): !![-24, 18, 5; 20, -15, -4; -5, 4, 1]
```
```lean
#cas [inverse] !![1, 2; 2, 4]
```
```output
Output (no inverse): the matrix is singular (determinant 0); Mathlib's A⁻¹ is 0
```

## In a proof
```lean
theorem inverse_two : (!![(1 : ℚ), 2; 3, 4])⁻¹ = !![-2, 1; 3 / 2, -1 / 2] := by
  cas
```

## See also
Mathematica `Inverse`, SymPy `Matrix.inv`. The modes `det`, `linearSolve` and `matrixPower`.

## Possible issues
```lean
#cas [inverse] !![1, 2, 3; 4, 5, 6]
```
```output
inverse: the matrix must be square
```
A matrix that is not square has no inverse. `#cas [linearSolve] (A, b)` solves `A *ᵥ x = b` for a
matrix of any shape.
-/
syntax (name := casInverseCommand) "#cas" "[" &"inverse" "]" term : command

/-- `#cas [transpose] A` computes the transpose of a matrix `A` with rational entries and proves it.

## Theorem
The report proves `A.transpose = B` for Mathlib's `Matrix.transpose` (written `Aᵀ`) over `ℚ`,
decided by kernel evaluation.

## Conditions and limits
`A` is a matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]` of any shape, and
each entry is a closed rational expression such as `-3/2`, `0.25` or `1/10^15`.

## Options
None.

## Examples
```lean
#cas [transpose] !![1, 2, 3; 4, 5, 6]
```
```output
Output (transpose): !![1, 4; 2, 5; 3, 6]
```
```lean
#cas [transpose] !![1, 2, 3]
```
```output
Output (transpose): !![1; 2; 3]
```

## In a proof
```lean
theorem transpose_two : !![(1 : ℚ), 2; 3, 4].transpose = !![1, 3; 2, 4] := by
  cas
```

## See also
Mathematica `Transpose`, SymPy `Matrix.T`. The modes `dot` and `trace`.

## Possible issues
```lean
#cas [transpose] !![1, 2; 3]
```
```output
the rows of the matrix have different lengths
```
Every row of the literal needs the same number of entries.
-/
syntax (name := casTransposeCommand) "#cas" "[" &"transpose" "]" term : command

/-- `#cas [trace] A` computes the trace of a square matrix `A` with rational entries and proves it.

## Theorem
The report proves `A.trace = t` for Mathlib's `Matrix.trace` over `ℚ`, the sum of the diagonal
entries, decided by kernel evaluation.

## Conditions and limits
`A` is a square matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]`, and each
entry is a closed rational expression such as `-3/2`, `0.25` or `1/10^15`.

## Options
None.

## Examples
```lean
#cas [trace] !![1, 2; 3, 4]
```
```output
Output (trace): 5
```
```lean
#cas [trace] !![1/2, 7; 0, 1/3]
```
```output
Output (trace): 5/6
```

## In a proof
```lean
theorem trace_two : Matrix.trace !![(1 : ℚ), 2; 3, 4] = 5 := by
  cas
```

## See also
Mathematica `Tr`, SymPy `Matrix.trace`. The modes `det`, `characteristicPolynomial` and
`eigenvalues`.

## Possible issues
```lean
#cas [trace] !![1, 2, 3; 4, 5, 6]
```
```output
trace: the matrix must be square
```
The trace is defined for square matrices only.
-/
syntax (name := casTraceCommand) "#cas" "[" &"trace" "]" term : command

/-- `#cas [matrixPower k] A` computes the power `A ^ k` of a square matrix `A` with rational entries
and proves it.

## Theorem
The report proves `A ^ k = B` for Mathlib's matrices over `ℚ`, decided by kernel evaluation.

## Conditions and limits
`k` is a natural literal with `k ≤ 1000`. `A` is a square matrix literal `!![a, b; c, d]` or a
list of rows `[[a, b], [c, d]]`, and each entry is a closed rational expression such as `-3/2`,
`0.25` or `1/10^15`.

## Options
None.

## Examples
```lean
#cas [matrixPower 10] !![1, 1; 1, 0]
```
```output
Output (power): !![89, 55; 55, 34]
```
```lean
#cas [matrixPower 3] !![1/2, 1; 0, 1/2]
```
```output
Output (power): !![1/8, 3/4; 0, 1/8]
```

## In a proof
```lean
theorem fibonacci_matrix : !![(1 : ℚ), 1; 1, 0] ^ 10 = !![89, 55; 55, 34] := by
  decide +kernel
```
Kernel evaluation, the proof of the report, decides the equation.

## See also
Mathematica `MatrixPower`, SymPy `Matrix.pow`. The modes `dot`, `inverse` and `eigenvalues`.

## Possible issues
```lean
#cas [matrixPower 1001] !![1, 1; 1, 0]
```
```output
matrixPower 1001: the power is decided by kernel evaluation, up to exponent 1000
```
In a proof, `pow_add` and `pow_mul` split a larger exponent into powers that the mode computes.
The exponent is a natural number; for a negative power, take the power of the matrix that
`#cas [inverse] A` prints.
-/
syntax (name := casMatrixPowerCommand) "#cas" "[" &"matrixPower" num "]" term : command

/-- `#cas [dot] (A, B)` computes the product of a matrix `A` and a matrix or vector `B` with
rational entries and proves it.

## Theorem
For a matrix `B` the report proves `A * B = C`, and for a vector `v` it proves `A.mulVec v = w`,
both for Mathlib's matrices over `ℚ` and decided by kernel evaluation (`decide +kernel`).

## Conditions and limits
`A` is a matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]`. `B` is a matrix
literal or a vector `![a, b]` or `[a, b]`, with as many rows or entries as `A` has columns. Each
entry is a closed rational expression such as `-3/2`, `0.25` or `1/10^15`.

## Options
None.

## Examples
```lean
#cas [dot] (!![1, 2; 3, 4], !![0, 1; 1, 0])
```
```output
Output (product): !![2, 1; 4, 3]
```
```lean
#cas [dot] (!![1, 2, 3; 4, 5, 6], ![1, 1, 1])
```
```output
Output (product): ![6, 15]
```

## In a proof
```lean
theorem dot_swap : !![(1 : ℚ), 2; 3, 4] * !![0, 1; 1, 0] = !![2, 1; 4, 3] := by
  cas
```

## See also
Mathematica `Dot`, SymPy `Matrix.multiply`. The modes `matrixPower`, `transpose` and
`linearSolve`.

## Possible issues
```lean
#cas [dot] (!![1, 2; 3, 4], ![1, 2, 3])
```
```output
dot: the sizes do not match
```
The number of columns of `A` and the length of `B` differ.
```lean
#cas [dot] (![1, 2], ![3, 4])
```
```output
expected a matrix `!![a, b; c, d]` or `[[a, b], [c, d]]`
```
The first factor is a matrix. For the dot product of two vectors, write the first one as a row:
`#cas [dot] (!![1, 2], ![3, 4])` gives `![11]`.
-/
syntax (name := casDotCommand) "#cas" "[" &"dot" "]" term : command

elab_rules : command
  | `(#cas [det] $A:term) => do
      unless ← Tactic.RouteRegistry.runCommandBackends `det (← getRef) do
        LinearAlgebra.logDet A A
  | `(#cas [inverse] $A:term) => LinearAlgebra.logInverse A A
  | `(#cas [transpose] $A:term) => LinearAlgebra.logArithmetic A .transpose A
  | `(#cas [trace] $A:term) => LinearAlgebra.logArithmetic A .trace A
  | `(#cas [matrixPower $k:num] $A:term) => LinearAlgebra.logArithmetic A (.power k.getNat) A
  | `(#cas [dot] $e:term) => do
      match e with
      | `(($A, $B)) => LinearAlgebra.logDot e A B
      | _ => throwErrorAt e "dot: expected a pair `(A, B)`"

end CAS.Command
