import tmp.sheaf.xif.paper.Mzk1F0CompositionLaws2Actual

/-! # Mzk1F0CompositionLaws3Actual — identity-composition laws for polyMapQbar (real)

Real Lean (no sorry/axiom): composing with the identity polynomial X on either side does not
change a P1(Qbar) polynomial map, chained over the PROVED polyMapQbar_comp and
polyMapQbar_X.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1F0CompositionLaws3Actual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1F0StepGeometryActual
open LeanFormal.IUT.XiFPaper.Mzk1F0CompositionLawsActual
open LeanFormal.IUT.XiFPaper.Mzk1F0CompositionLaws2Actual

universe u

/-- Right identity: polyMapQbar (f.comp X) = polyMapQbar f. -/
theorem polyMapQbar_comp_X (f : Polynomial ℚ) :
    polyMapQbar (f.comp Polynomial.X) = polyMapQbar f := by
  rw [polyMapQbar_comp, polyMapQbar_X, Function.comp_id]

/-- Left identity: polyMapQbar (X.comp f) = polyMapQbar f. -/
theorem polyMapQbar_X_comp (f : Polynomial ℚ) :
    polyMapQbar (Polynomial.X.comp f) = polyMapQbar f := by
  rw [Polynomial.X_comp]

/-- f0-map is unchanged when the inner polynomial is composed with X. -/
theorem f0Map_comp_X (alpha0 : Qbar) (g : Polynomial ℚ) :
    f0Map alpha0 ∘ polyMapQbar (g.comp Polynomial.X) = f0Map alpha0 ∘ polyMapQbar g := by
  rw [polyMapQbar_comp_X]

#check polyMapQbar_comp_X
#check f0Map_comp_X

end LeanFormal.IUT.XiFPaper.Mzk1F0CompositionLaws3Actual
end
