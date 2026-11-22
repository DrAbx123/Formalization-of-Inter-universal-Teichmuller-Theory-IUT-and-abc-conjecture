import tmp.sheaf.xif.paper.S2278QHomNaturalityActual
import tmp.sheaf.xif.paper.S2192QHomSheavesActual

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2278QHomNaturalityActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S2267QHomEqualizerMulActionActual
open LeanFormal.IUT.XiFPaper.S2192QHomSheavesActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2283QHomEqualizerFinal3Actual

variable (S : Iut.SchemeOverField S1726K)

/-- Actual slice naturality of P_T and Q_T, re-exported. -/
theorem S2283PT_natural
    (M : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))
    {T₁ T₂ : (Over S)ᵒᵖ} (p : T₁ ⟶ T₂) :
    p.unop.left ≫ S2267PT S M T₁ = S2267PT S M T₂ :=
  S2278PT_natural S M p

/-- Exact first missing for the R.map naturality step: the representable
R.map formula is not yet unfolded in Lean. -/
def S2283RMapFormulaFirstMissing : Prop :=
  Nonempty (HasWeakSheafify ((Iut.SchemeOverField.etaleTopology S1726K).over S) Type)

end LeanFormal.IUT.XiFPaper.S2283QHomEqualizerFinal3Actual

end
