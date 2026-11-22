import tmp.sheaf.xif.paper.S2168QHomSheafEqualizerActual
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Sites.Limits

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2168QHomSheafEqualizerActual
open LeanFormal.IUT.XiFPaper.S2160QHomSheafActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2181EqualizerSheafActual

universe v

/-- The required Mathlib equalizer sheaf lemma is actually true: the pointwise
equalizer of two morphisms of sheaves of types is a sheaf. -/
theorem S2181EqualizerSheafLemma (C : Type 1) [Category.{v} C]
    (J : GrothendieckTopology C) :
    S2168EqualizerSheafLemma C J := by
  intro P R hP hR f g
  let F : WalkingParallelPair ⥤ (Cᵒᵖ ⥤ Type) := Limits.parallelPair f g
  have hF : forall j : WalkingParallelPair, Presheaf.IsSheaf J (F.obj j) := by
    intro j
    rcases j with _ | _
    · simpa [F, Limits.parallelPair] using hP
    · simpa [F, Limits.parallelPair] using hR
  have h := ObjectProperty.prop_limit (P := Presheaf.IsSheaf J) (F := F) hF
  simpa [Limits.equalizer, F] using h

/-- The Q hom-presheaf sheaf condition now reduces to the equalizer
identification alone; the equalizer sheaf lemma is proved. -/
theorem S2181QHomSheafFor_of_identification
    (hId : S2168QHomEqualizerIdentification) :
    S2160QHomSheafFor :=
  S2160QHomSheafFor_of_equalizer
    (fun S => S2181EqualizerSheafLemma (Over S)
      ((Iut.SchemeOverField.etaleTopology S1726K).over S))
    hId

/-- The remaining first missing for the Q hom-presheaf: exhibit the equalizer
data for each S,M,N. -/
def S2181QHomEqualizerIdentificationFirstMissing : Prop :=
  S2168QHomEqualizerIdentification

/-- Conditional actual: equalizer identification gives the prestack half. -/
theorem S2181QHomSheafFor_of_equalizerIdentification
    (h : S2181QHomEqualizerIdentificationFirstMissing) :
    S2160QHomSheafFor :=
  S2181QHomSheafFor_of_identification h

#print axioms S2181EqualizerSheafLemma
#print axioms S2181QHomSheafFor_of_identification

end LeanFormal.IUT.XiFPaper.S2181EqualizerSheafActual

end
