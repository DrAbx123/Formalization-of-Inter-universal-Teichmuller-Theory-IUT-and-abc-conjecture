import tmp.sheaf.xif.paper.S2303EvalDiagramProofActual
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2303EvalDiagramProofActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S2206PConstantSheafActual
open LeanFormal.IUT.XiFPaper.S2192QHomSheavesActual
open LeanFormal.IUT.XiFPaper.S2285RMapNatActual
open LeanFormal.IUT.XiFPaper.S2271QHomEqualizerNatActual
open LeanFormal.IUT.XiFPaper.S2267QHomEqualizerMulActionActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2308EqualizerIsoFinalActual

variable (S : Iut.SchemeOverField S1726K)
variable (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))
variable (T : (Over S)ᵒᵖ)

/-- Pointwise equalizer object iso using the evaluated diagram iso. -/
noncomputable def S2308EqualizerObjIso :
    (Limits.equalizer (S2285f S M) (S2285g S N)).obj T ≅
      Limits.equalizer ((S2285f S M).app T) ((S2285g S N).app T) := by
  let e₁ := limitObjIsoLimitCompEvaluation
    (Limits.parallelPair (S2285f S M) (S2285g S N)) T
  let e₂ := HasLimit.isoOfNatIso (S2303EvalDiagramIso S M N T)
  exact e₁ ≪≫ e₂

#print axioms S2308EqualizerObjIso

end LeanFormal.IUT.XiFPaper.S2308EqualizerIsoFinalActual

end
