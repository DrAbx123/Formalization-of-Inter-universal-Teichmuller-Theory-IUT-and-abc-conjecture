import tmp.sheaf.xif.paper.S2259QMapPrecompActual
import tmp.sheaf.xif.paper.S2251QHomEqualizerType1Actual

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2259QMapPrecompActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S2251QHomEqualizerType1Actual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2263QHomEqualizerFinalActual

variable (S : Iut.SchemeOverField S1726K)

/-- Re-export of the actual Q.map identification. -/
theorem S2263QMapPrecomp {U V : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ}
    (f : U ⟶ V) :
    (S2152Q.map f).toFunctor = S1971PrecompFunctor f :=
  S2259QMapPrecomp U V f

/-- The exact first missing for the Type 1 equalizer identification: the
pointwise P_T/Q_T extraction together with the naturality and ULift iso. -/
def S2263FirstMissing : Prop :=
  Nonempty (HasWeakSheafify ((Iut.SchemeOverField.etaleTopology S1726K).over S) Type)

end LeanFormal.IUT.XiFPaper.S2263QHomEqualizerFinalActual

end
