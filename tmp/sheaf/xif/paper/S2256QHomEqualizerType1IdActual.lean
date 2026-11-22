import tmp.sheaf.xif.paper.S2255QHomEqualizerType1IdActual

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2255QHomEqualizerType1IdActual
open LeanFormal.IUT.XiFPaper.S2251QHomEqualizerType1Actual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2256QHomEqualizerType1IdActual

variable (S : Iut.SchemeOverField S1726K)

/-- Type 1 P is actual from S2246/S2251. -/
noncomputable abbrev S2256P :
    Sheaf ((Iut.SchemeOverField.etaleTopology S1726K).over S) (Type 1) :=
  S2255P S

/-- Type 0 R is actual from S2192. -/
noncomputable abbrev S2256R : ((Over S)ᵒᵖ ⥤ Type) :=
  S2255R S

/-- The pointwise subtype characterization of the Q hom-presheaf.  This is the
formula supplied by S1971PointwiseQuotient_hom; it is recorded as the exact
remaining bridge, not proved in this file. -/
def S2256QHomSubtypeBridge : Prop :=
  S2251Type0Bridge S

/-- Exact first missing for the Type 1 equalizer identification: the ULift
bridge together with the equalizer identification. -/
def S2256FirstMissing : Prop := S2256QHomSubtypeBridge S

#print axioms S2251P_isSheaf

end LeanFormal.IUT.XiFPaper.S2256QHomEqualizerType1IdActual

end
