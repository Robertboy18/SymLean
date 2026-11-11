/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Expr.Simplify

/-!
# Elementary symbolic antiderivative candidates

The elementary rule table of symbolic integration: powers, exponentials, trigonometric
functions, logarithms, arctangents, square roots, and their compositions with an inner
expression whose derivative in the selected coordinate is constant.

Supported rules include:

* constants and powers of the selected variable;
* sums, differences, negations, and multiplication or division by expressions
  independent of the selected variable;
* exponential, sine, cosine, logarithm, inverse-trigonometric, and square-root
  primitives after affine-style substitution;
* reciprocal and reciprocal-square-root forms whose inner expression has a
  nonzero derivative independent of the selected variable, and the arctangent
  form `a / (c ^ 2 + u ^ 2)` with a constant `c` (`arctanCandidate?`);
* real powers `u ^ c` with a constant exponent `c ≠ -1` and an inner expression
  with constant nonzero derivative (the real power rule).

Unsupported forms return `none`, allowing the planner to continue with
substitution, rational reduction, recurrence solving, or integration by parts.

## Implementation notes

For a composition `f u` we return `F u / d`, where `F` is the classical primitive of `f` and
`d` is the derivative of the inner expression `u`. `nonzeroIndependentDerivative?` computes `d`
symbolically and accepts it only when it is not literally zero and is free of the selected
variable, so that the chain rule gives back `f u`. When `d` contains parameters it may still
vanish; the candidate divides by `d`, so its nonvanishing becomes a requirement of the
certificate.

The table only generates candidates. Given a selected variable `v`,
`Elementary.candidate? v expr` may propose an expression whose derivative is expected to equal
`expr`, but nothing here proves it. The integration planner checks proposed derivatives during
search, and `integrate?` accepts a result only after constructing an
`IntegrationCheck.AntiderivativeCert` with all required analytic side conditions.
-/

@[expose] public section

namespace CAS.IntegrationPlanner.Elementary

open CAS.Verified.Expr

/--
Antiderivative candidate `v ^ (k + 1) / (k + 1)` for the power `v ^ k` of the selected
variable `v`.
-/
def variablePowerCandidate {ι : Type*} (v : ι) (k : Nat) : Verified.Expr ι :=
  mkDiv (mkPow (.var v) (k + 1)) (.nat (k + 1))

/--
Return the simplified derivative of `arg` when it is not literal zero and
does not contain the selected variable.

This recognizes the constant Jacobian needed by the table's elementary
substitution rules. A parameter-dependent derivative may still vanish at some
points; its nonvanishing is an obligation of the final certificate, not a fact
proved by this syntax check. Rejecting variable-dependent derivatives leaves
nonlinear substitution to the general planner.
-/
def nonzeroIndependentDerivative? {ι : Type*} [DecidableEq ι] (v : ι)
    (arg : Verified.Expr ι) : Option (Verified.Expr ι) :=
  let d := Verified.Expr.simplify (arg.diff v)
  if d = 0 then none
  else if Verified.Expr.containsVar v d = false then some d
  else none

/--
Antiderivative candidate for `a / (constantPart + variablePart)` when the denominator is a sum
of squares `c ^ 2 + u ^ 2` with `c` independent of `v` and `u` of nonzero derivative `u'`
independent of `v`: `a * atan (u / c) / (c * u')`. The constant part may be the literal `1`
(then the candidate is `a * atan u / u'`), a perfect-square natural literal, or a square
`c ^ 2` of a symbolic constant; the two summands may come in either order, and the caller
tries both. The planner's derivative check and the public residual certificate decide whether
the proposal is right, so this table entry proves nothing by itself.

This entry also works with symbolic coefficients, where the univariate rational
integrator is unavailable. Nonvanishing of `c` and `u'` remains a certificate obligation.
-/
def arctanCandidate? {ι : Type*} [DecidableEq ι] (v : ι)
    (a constantPart variablePart : Verified.Expr ι) : Option (Verified.Expr ι) :=
  match variablePart with
  | .pow arg 2 =>
      if Verified.Expr.containsVar v constantPart then
        none
      else
        match nonzeroIndependentDerivative? v arg with
        | none => none
        | some d =>
            match constantPart with
            | .nat 1 => some (mkDiv (mkMul a (.atan arg)) d)
            | .nat k =>
                let root := Nat.sqrt k
                if 0 < k ∧ root * root = k then
                  some (mkDiv (mkMul a (.atan (mkDiv arg (.nat root))))
                    (mkMul (.nat root) d))
                else
                  none
            | .pow c 2 => some (mkDiv (mkMul a (.atan (mkDiv arg c))) (mkMul c d))
            | _ => none
  | _ => none

/--
Propose an elementary antiderivative of `expr` with respect to `v`.

This executable table performs search only: a returned candidate carries no
correctness claim. Callers must differentiate it and discharge every validity,
positivity, and nonvanishing condition before exposing it as a verified
antiderivative.
-/
def candidate? {ι : Type*} [DecidableEq ι] (v : ι) :
    Verified.Expr ι → Option (Verified.Expr ι)
  | .add a b => do
      let candidateA ← candidate? v a
      let candidateB ← candidate? v b
      some (mkAdd candidateA candidateB)
  | .sub a b => do
      let candidateA ← candidate? v a
      let candidateB ← candidate? v b
      some (mkSub candidateA candidateB)
  | .neg a => do
      let candidateA ← candidate? v a
      some (mkNeg candidateA)
  | .mul a b =>
      if Verified.Expr.containsVar v a = false then
        match candidate? v b with
        | some candidateB => some (mkMul a candidateB)
        | none => none
      else if Verified.Expr.containsVar v b = false then
        match candidate? v a with
        | some candidateA => some (mkMul b candidateA)
        | none => none
      else
        none
  | .div a b =>
      if Verified.Expr.containsVar v b = false then
        match candidate? v a with
        | some candidateA => some (mkDiv candidateA b)
        | none => none
      else if Verified.Expr.containsVar v a = false then
        match b with
        | .sqrt (.sub (.nat 1) (.pow arg 2)) =>
            match nonzeroIndependentDerivative? v arg with
            | some d => some (mkDiv (mkMul a (.asin arg)) d)
            | none => none
        | .sqrt arg =>
            match nonzeroIndependentDerivative? v arg with
            | some d => some (mkDiv
                (mkMul (mkMul 2 a) (mkSqrt arg)) d)
            | none => none
        | .add p q =>
            match arctanCandidate? v a p q with
            | some candidate => some candidate
            | none =>
                match arctanCandidate? v a q p with
                | some candidate => some candidate
                | none =>
                    match nonzeroIndependentDerivative? v b with
                    | some d => some (mkMul a (mkDiv (mkLog b) d))
                    | none => none
        | _ =>
            match nonzeroIndependentDerivative? v b with
            | some d => some (mkMul a
                (mkDiv (mkLog b) d))
            | none => none
      else
        none
  | .var x =>
      if x = v then some (variablePowerCandidate v 1)
      else some (mkMul (.var x) (.var v))
  | .pow (.var x) k =>
      if x = v then some (variablePowerCandidate v k)
      else some (mkMul (.pow (.var x) k) (.var v))
  | .pow arg k =>
      if Verified.Expr.containsVar v arg = false then
        some (mkMul (.pow arg k) (.var v))
      else
        match nonzeroIndependentDerivative? v arg with
        | some d => some (mkDiv (mkPow arg (k + 1))
            (mkMul (.nat (k + 1)) d))
        | none => none
  | .exp arg =>
      if Verified.Expr.containsVar v arg = false then
        some (mkMul (.exp arg) (.var v))
      else
        match nonzeroIndependentDerivative? v arg with
        | some d => some (mkDiv (.exp arg) d)
        | none => none
  | .sin arg =>
      if Verified.Expr.containsVar v arg = false then
        some (mkMul (.sin arg) (.var v))
      else
        match nonzeroIndependentDerivative? v arg with
        | some d => some (mkDiv (mkNeg (.cos arg)) d)
        | none => none
  | .cos arg =>
      if Verified.Expr.containsVar v arg = false then
        some (mkMul (.cos arg) (.var v))
      else
        match nonzeroIndependentDerivative? v arg with
        | some d => some (mkDiv (.sin arg) d)
        | none => none
  | .atan arg =>
      if Verified.Expr.containsVar v arg = false then
        some (mkMul (.atan arg) (.var v))
      else
        match nonzeroIndependentDerivative? v arg with
        | some d =>
            some (mkDiv
              (mkSub (mkMul arg (.atan arg))
                (mkDiv
                  (mkLog (mkAdd 1 (mkPow arg 2))) 2))
              d)
        | none => none
  | .asin arg =>
      if Verified.Expr.containsVar v arg = false then
        some (mkMul (.asin arg) (.var v))
      else
        match nonzeroIndependentDerivative? v arg with
        | some d =>
            some (mkDiv
              (mkAdd (mkMul arg (.asin arg))
                (mkSqrt (mkSub 1 (mkPow arg 2))))
              d)
        | none => none
  | .acos arg =>
      if Verified.Expr.containsVar v arg = false then
        some (mkMul (.acos arg) (.var v))
      else
        match nonzeroIndependentDerivative? v arg with
        | some d =>
            some (mkDiv
              (mkSub (mkMul arg (.acos arg))
                (mkSqrt (mkSub 1 (mkPow arg 2))))
              d)
        | none => none
  | .log arg =>
      if Verified.Expr.containsVar v arg = false then
        some (mkMul (.log arg) (.var v))
      else
        match nonzeroIndependentDerivative? v arg with
        | some d => some (mkDiv
            (mkSub (mkMul arg (mkLog arg)) arg) d)
        | none => none
  | .sqrt arg =>
      if Verified.Expr.containsVar v arg = false then
        some (mkMul (.sqrt arg) (.var v))
      else
        match nonzeroIndependentDerivative? v arg with
        | some d => some (mkDiv
            (mkMul 2 (mkPow (mkSqrt arg) 3))
            (mkMul 3 d))
        | none => none
  | .rpow arg exponent =>
      if Verified.Expr.containsVar v exponent then
        none
      else if Verified.Expr.containsVar v arg = false then
        some (mkMul (.rpow arg exponent) (.var v))
      else
        -- The real power rule `∫ u ^ c u' = u ^ (c + 1) / (c + 1)` for a constant exponent
        -- `c ≠ -1`. The exponent `c + 1` is only simplified structurally; the search checker
        -- and the certificate route normalize the exponent arithmetic of the residual.
        let shifted := Verified.Expr.simplify (mkAdd exponent 1)
        if shifted = 0 then
          none
        else
          match nonzeroIndependentDerivative? v arg with
          | some d => some (mkDiv (.rpow arg shifted) (mkMul shifted d))
          | none => none
  | expr =>
      if Verified.Expr.containsVar v expr = false then
        some (mkMul expr (.var v))
      else
        none

end CAS.IntegrationPlanner.Elementary
