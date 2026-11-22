import tmp.sheaf.xif.paper.S2251QHomEqualizerType1Actual

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2251QHomEqualizerType1Actual
open LeanFormal.IUT.XiFPaper.S2246PConstantSheaf2Actual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2255QHomEqualizerType1IdActual

variable (S : Iut.SchemeOverField S1726K)

/-- Type 1 P is the actual lifted constant sign group sheaf. -/
noncomputable abbrev S2255P :
    Sheaf ((Iut.SchemeOverField.etaleTopology S1726K).over S) (Type 1) :=
  S2251P S

/-- Type 1 R is the lifted representable morphism sheaf. -/
noncomputable abbrev S2255R : ((Over S)ᵒᵖ ⥤ Type) :=
  S2251R S

/-- The exact Type 1 identification missing: for each M N, an isomorphism
between the ULift of the Type 0 Q hom-presheaf and the equalizer of two maps
f,g built from P_T and Q_T.  This is recorded as an abstract proposition because
the ULift bridge and the naturality of f,g are not yet constructed. -/
def S2255Type1EqualizerIdentification : Prop :=
  S2251Type0Bridge S

/-- The exact first missing for the Type 1 route. -/
def S2255FirstMissing : Prop := S2255Type1EqualizerIdentification S

#print axioms S2251P_isSheaf

end LeanFormal.IUT.XiFPaper.S2255QHomEqualizerType1IdActual

end
