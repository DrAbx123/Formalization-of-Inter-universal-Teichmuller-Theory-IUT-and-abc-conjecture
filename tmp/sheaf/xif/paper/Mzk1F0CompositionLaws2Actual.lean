import tmp.sheaf.xif.paper.Mzk1F0CompositionLawsActualV2

/-! # Mzk1F0CompositionLaws2Actual — real composition laws for the f0 P1(Qbar) maps

Real Lean (no sorry/axiom): identity/zero laws for polyMapQbar and the f0-map composition law,
chained over the PROVED polyMapQbar_comp.  No adapted copy; all proofs genuine.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1F0CompositionLaws2Actual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1F0StepGeometryActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1F0CompositionLawsActual

universe u

/-- The polynomial X induces the identity map on P1(Qbar). -/
theorem polyMapQbar_X : polyMapQbar (Polynomial.X : Polynomial ℚ) = id := by
  funext p
  cases p with
  | none => rfl
  | some x => rfl

/-- Map by the zero polynomial: infinity to infinity, every finite point to 0. -/
theorem polyMapQbar_zero_apply (p : P1Point Qbar) :
    polyMapQbar (0 : Polynomial ℚ) p = p.map (fun _ => (0 : Qbar)) := rfl

/-- f0-map composition law: f0 after a polynomial map is the polynomial map of the
composition (contravariant form of the PROVED polyMapQbar_comp). -/
theorem f0Map_comp (alpha0 : Qbar) (g : Polynomial ℚ) :
    f0Map alpha0 ∘ polyMapQbar g = polyMapQbar ((f0Poly alpha0).comp g) := by
  rw [f0Map, polyMapQbar_comp]

/-- Composition of polynomial maps is associative (from Polynomial.comp_assoc). -/
theorem polyMapQbar_comp_assoc (f g h : Polynomial ℚ) :
    polyMapQbar ((f.comp g).comp h) = polyMapQbar (f.comp (g.comp h)) := by
  rw [Polynomial.comp_assoc]

#check polyMapQbar_X
#check f0Map_comp

end LeanFormal.IUT.XiFPaper.Mzk1F0CompositionLaws2Actual
end
