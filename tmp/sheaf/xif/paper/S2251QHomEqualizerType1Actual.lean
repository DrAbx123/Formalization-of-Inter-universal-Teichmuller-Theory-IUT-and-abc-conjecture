import tmp.sheaf.xif.paper.S2246PConstantSheaf2Actual

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2246PConstantSheaf2Actual
open LeanFormal.IUT.XiFPaper.S2192QHomSheavesActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2251QHomEqualizerType1Actual

variable (S : Iut.SchemeOverField S1726K)

/-- The actual Type 1 lifted constant sign group sheaf. -/
noncomputable abbrev S2251P : Sheaf ((Iut.SchemeOverField.etaleTopology S1726K).over S) (Type 1) :=
  S2246P S

/-- Its actual sheaf property. -/
theorem S2251P_isSheaf :
    Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology S1726K).over S)
      (S2251P S).1 :=
  S2246P_isSheaf S

/-- The exact Type 0 bridge still missing for the original Q hom Type 0 values. -/
def S2251Type0Bridge : Prop :=
  Nonempty (HasWeakSheafify ((Iut.SchemeOverField.etaleTopology S1726K).over S) Type)

/-- The Type 1 equalizer identification is not constructed; the first missing
remains the Type 0 bridge (or a parallel Type 1 identification for the ULift of
the Q hom presheaf). -/
def S2251FirstMissing : Prop := S2251Type0Bridge S

/-- The Type 1 R sheaf from S2192/S2246 is actual. -/
noncomputable abbrev S2251R : ((Over S)ᵒᵖ ⥤ Type) :=
  S2192R S

#print axioms S2251P_isSheaf

end LeanFormal.IUT.XiFPaper.S2251QHomEqualizerType1Actual

end
