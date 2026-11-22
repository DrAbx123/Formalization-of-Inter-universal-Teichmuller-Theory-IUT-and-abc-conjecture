import tmp.sheaf.xif.paper.Mzk1F0StepGeometryActual

/-!
  Mainline: composition laws for the Q-polynomial P1(Qbar) maps used in the f0 step
  (Problem C geometric layer).  Real proofs; the named paper transport is untouched.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1F0CompositionLawsV2Actual

noncomputable section

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1F0StepGeometryActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

/-- Polynomial maps on P1(Qbar) compose contravariantly (composition of polynomials). -/
theorem polyMapQbar_comp (f g : Polynomial ℚ) :
    polyMapQbar (f.comp g) = polyMapQbar f ∘ polyMapQbar g := by
  funext p
  cases p with
  | none => rfl
  | some x =>
      simp [polyMapQbar, Polynomial.aeval_comp]



end

end LeanFormal.IUT.XiFPaper.Mzk1F0CompositionLawsV2Actual