import tmp.sheaf.xif.paper.S2158QStackActual
import Mathlib.CategoryTheory.Sites.SheafOfTypes

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2158QStackActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2160QHomSheafActual

/-- The hom-presheaf sheaf condition for the constructed Q. -/
def S2160QHomSheafFor : Prop := S2158QHomSheaf

/-- The exact first missing for the prestack half of Q. -/
def S2160QHomSheafFirstMissing : Prop := S2160QHomSheafFor

/-- The exact first missing is the S2158 prestack half. -/
theorem S2160QHomSheafFirstMissing_iff_S2158 :
    S2160QHomSheafFirstMissing ↔ S2158QHomSheaf :=
  Iff.rfl

/-- Conditional actual: the prestack half contributes the first conjunct of the
S2158 required API. -/
theorem S2158QPrestack_of_homSheafFirstMissing
    (h : S2160QHomSheafFirstMissing) : S2158QPrestack :=
  S2158QPrestack_iff_homSheaf.mpr h

/-- The remaining effective-descent input is independent. -/
def S2160QEffectiveDescent (l : PrimeGeFive) : Prop :=
  S2158QEffectiveDescent l

/-- Prestack half together with effective descent is exactly the S2158 API. -/
theorem S2160QRequiredAPI_iff (l : PrimeGeFive) :
    S2160QHomSheafFirstMissing ∧ S2160QEffectiveDescent l ↔
      Nonempty (S2158QRequiredAPI l) := by
  constructor
  · rintro ⟨hH, hD⟩
    exact ⟨⟨S2158QPrestack_of_homSheafFirstMissing hH, hD⟩⟩
  · rintro ⟨h⟩
    exact ⟨S2158QPrestack_iff_homSheaf.mp h.prestack, h.effective⟩

#print axioms S2160QHomSheafFirstMissing_iff_S2158
#print axioms S2158QPrestack_of_homSheafFirstMissing
#print axioms S2160QRequiredAPI_iff

end LeanFormal.IUT.XiFPaper.S2160QHomSheafActual

end
