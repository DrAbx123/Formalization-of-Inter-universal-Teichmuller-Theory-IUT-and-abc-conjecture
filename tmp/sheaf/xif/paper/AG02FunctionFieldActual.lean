import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# AG02: function field of an integral scheme (Mathlib-based foundation)

Source-layer AG infrastructure.  Mathlib already provides the function field of
an integral scheme and the order of vanishing at codimension-one points:
* AlgebraicGeometry.Scheme.functionField (FunctionField.lean:37),
  Field instance :51, germToFunctionField :42, germ injectivity :65,
  functionField_isFractionRing_of_isAffineOpen :148;
* AlgebraicGeometry.Scheme.ord (OrderOfVanishing.lean:52), ord_mul :81,
  ord_zero :64, ord_of_isUnit :88, ord_add :107, ord_le_smul :119.
This file REUSES them (no re-proof) and exposes the paper-facing interface.

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.AG02FunctionFieldActual

open AlgebraicGeometry Order TopologicalSpace WithZero

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- Codimension-one points of a scheme (the support of Weil divisors). -/
abbrev AGCodimOnePoint (X : Scheme.{u}) : Type u := {z : X // coheight z = 1}

/-- The order of vanishing of a function field element at a codimension-one point. -/
def agOrderOfVanishing (f : X.functionField) (z : AGCodimOnePoint X) : ℤ :=
  X.ord f z.1

/-- Multiplicativity of the order of vanishing (reused Mathlib ord_mul). -/
theorem agOrderOfVanishing_mul {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0)
    (z : AGCodimOnePoint X) :
    agOrderOfVanishing (f * g) z = agOrderOfVanishing f z + agOrderOfVanishing g z :=
  Scheme.ord_mul hf hg

/-- The order of vanishing of the zero function is zero. -/
@[simp]
theorem agOrderOfVanishing_zero (z : AGCodimOnePoint X) :
    agOrderOfVanishing (0 : X.functionField) z = 0 := by
  simp [agOrderOfVanishing]

/-- A unit section has vanishing order zero at every point of its open set
(reused Mathlib ord_of_isUnit). -/
theorem agOrderOfVanishing_germ_of_isUnit {U : X.Opens} [Nonempty U]
    {f : Γ(X, U)} (hf : IsUnit f) {x : X} (hx : x ∈ U) (hx1 : coheight x = 1) :
    agOrderOfVanishing (X.germToFunctionField U f) ⟨x, hx1⟩ = 0 :=
  Scheme.ord_of_isUnit hf hx

/-- The function field of an integral affine open is a fraction field of its
sections (reused Mathlib functionField_isFractionRing_of_isAffineOpen). -/
theorem agFunctionField_isFractionRing_of_isAffineOpen (U : X.Opens)
    (hU : IsAffineOpen U) [Nonempty U] :
    IsFractionRing Γ(X, U) X.functionField :=
  functionField_isFractionRing_of_isAffineOpen X U hU

/-- The germ map into the function field is injective on a nonempty open
(reused Mathlib germToFunctionField_injective). -/
theorem agGermToFunctionField_injective (U : X.Opens) [Nonempty U] :
    Function.Injective (X.germToFunctionField U) :=
  Scheme.germToFunctionField_injective X U

end LeanFormal.IUT.XiFPaper.AG02FunctionFieldActual

end
