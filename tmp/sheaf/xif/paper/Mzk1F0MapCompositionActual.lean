import tmp.sheaf.xif.paper.Mzk1F0CompositionLaws3Actual

/-! # Mzk1F0MapCompositionActual — composition of f0 maps (real)

Real Lean (no sorry/axiom): the composite of two f0 P1(Qbar) maps is the polynomial map of
the composed defining polynomials (contravariant composition law).  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1F0MapCompositionActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1F0StepGeometryActual
open LeanFormal.IUT.XiFPaper.Mzk1F0CompositionLawsActual

universe u

/-- Composite of two f0 maps is the polynomial map of the composed polynomials. -/
theorem f0Map_comp_f0Map (alpha0 beta0 : Qbar) :
    f0Map alpha0 ∘ f0Map beta0 = polyMapQbar ((f0Poly alpha0).comp (f0Poly beta0)) := by
  rw [f0Map, f0Map, polyMapQbar_comp]

/-- Pointwise form of the composition law. -/
theorem f0Map_f0Map_apply (alpha0 beta0 : Qbar) (p : P1Point Qbar) :
    f0Map alpha0 (f0Map beta0 p) =
      polyMapQbar ((f0Poly alpha0).comp (f0Poly beta0)) p := by
  rw [← f0Map_comp_f0Map]

/-- Composition after collapsing a polynomial map to f0 form. -/
theorem f0Map_polyMapQbar_apply (alpha0 : Qbar) (g : Polynomial ℚ) (p : P1Point Qbar) :
    f0Map alpha0 (polyMapQbar g p) =
      polyMapQbar ((f0Poly alpha0).comp g) p := by
  rw [f0Map_comp]

#check f0Map_comp_f0Map

end LeanFormal.IUT.XiFPaper.Mzk1F0MapCompositionActual
end
