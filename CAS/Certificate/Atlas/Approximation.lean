/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Certificate.Approximation
public import CAS.Certificate.Atlas.Basic

/-!
# Approximation certificate atlases

An `ApproxAtlasCert` holds an `ApproxCert` on every patch of a cover. The local endpoint
functions must equal shared global functions, while the local budgets need only be at most
the global one. `ApproxAtlasCert.sound` assembles them into one `ApproxOn` statement on
the covered domain.

## Implementation notes

We store the two endpoint functions as one function into `E × E`, so the shared carrier
`FunctionBudgetAtlasCert` needs a single agreement field; `cert_lhs` and `cert_rhs` take it
apart. `sound` applies `PatchCover.lift` to the local `sound` proofs and weakens each local budget
to `eps`. `toApproxCert` forgets the cover, and CEGA receives approximation atlases in that form.
-/

@[expose] public section

namespace CAS.Certificate

open CAS.Domain

/--
Local approximation certificates with shared endpoint functions and a global error budget.

The two endpoint functions are stored as one paired function in the common atlas structure; the
projections below recover them.
-/
abbrev ApproxAtlasCert (α E ι : Type*) [NormedAddCommGroup E]
    (domain : Set α) :=
  FunctionBudgetAtlasCert α (E × E) ι domain
    (ApproxCert α E)
    (fun cert x ↦ (cert.lhs x, cert.rhs x))
    (fun cert ↦ cert.eps)

namespace ApproxAtlasCert

variable {α E ι : Type*} [NormedAddCommGroup E] {domain : Set α}

/-- Global left-hand function. -/
abbrev lhs (c : ApproxAtlasCert α E ι domain) : α → E :=
  fun x ↦ (c.fn x).1

/-- Global right-hand function. -/
abbrev rhs (c : ApproxAtlasCert α E ι domain) : α → E :=
  fun x ↦ (c.fn x).2

/-- Global approximation-error budget. -/
abbrev eps (c : ApproxAtlasCert α E ι domain) : ℝ :=
  c.budget

/-- Every local left-hand function agrees with the global one. -/
theorem cert_lhs (c : ApproxAtlasCert α E ι domain) (i : ι) :
    (c.onPatch i).lhs = c.lhs :=
  funext fun x ↦ congrArg Prod.fst (congrFun (c.cert_fn i) x)

/-- Every local right-hand function agrees with the global one. -/
theorem cert_rhs (c : ApproxAtlasCert α E ι domain) (i : ι) :
    (c.onPatch i).rhs = c.rhs :=
  funext fun x ↦ congrArg Prod.snd (congrFun (c.cert_fn i) x)

/-- Every local error budget is bounded by the global budget. -/
theorem cert_eps (c : ApproxAtlasCert α E ι domain) (i : ι) :
    (c.onPatch i).eps ≤ c.eps :=
  c.cert_budget i

/-- Assemble the local estimates into a uniform approximation on the covered domain. -/
theorem sound (c : ApproxAtlasCert α E ι domain) :
    ApproxOn c.lhs c.rhs domain c.eps :=
  c.cover.lift fun i y hy ↦ le_trans
    (by simpa [c.cert_lhs i, c.cert_rhs i] using (c.onPatch i).sound y hy) (c.cert_eps i)

/-- Project an atlas to a global approximation certificate. -/
def toApproxCert (c : ApproxAtlasCert α E ι domain) : ApproxCert α E domain :=
  ApproxCert.ofApproxOn c.lhs c.rhs c.eps c.sound

/--
Build a two-patch approximation atlas.

The global error budget is the maximum of the two local budgets.
-/
def ofBinaryCover {left right : Set α} (hcover : domain ⊆ left ∪ right)
    (leftCert : ApproxCert α E left) (rightCert : ApproxCert α E right)
    (hlhs : rightCert.lhs = leftCert.lhs) (hrhs : rightCert.rhs = leftCert.rhs) :
    ApproxAtlasCert α E Bool domain :=
  FunctionBudgetAtlasCert.ofBinaryCover hcover leftCert rightCert <| by
    funext x
    rw [hlhs, hrhs]

end ApproxAtlasCert

end CAS.Certificate
