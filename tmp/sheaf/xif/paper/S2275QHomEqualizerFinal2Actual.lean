import tmp.sheaf.xif.paper.S2271QHomEqualizerNatActual
import tmp.sheaf.xif.paper.S2251QHomEqualizerType1Actual

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2271QHomEqualizerNatActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S2267QHomEqualizerMulActionActual
open LeanFormal.IUT.XiFPaper.S2251QHomEqualizerType1Actual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2275QHomEqualizerFinal2Actual

variable (S : Iut.SchemeOverField S1726K)

/-- Re-export of the actual pointwise subtype formula. -/
theorem S2275QHomObj_eq_subtype
    (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))
    (T : (Over S)ᵒᵖ) :
    (S2152Q.presheafHom M N).obj T =
      {g : Iut.SignGroup // g • S2267PT S M T = S2267QT S N T} :=
  S2271QHomObj_eq_subtype S M N T

/-- Exact first missing for the naturality/equalizer package. -/
def S2275FirstMissing : Prop :=
  Nonempty (HasWeakSheafify ((Iut.SchemeOverField.etaleTopology S1726K).over S) Type)

end LeanFormal.IUT.XiFPaper.S2275QHomEqualizerFinal2Actual

end
