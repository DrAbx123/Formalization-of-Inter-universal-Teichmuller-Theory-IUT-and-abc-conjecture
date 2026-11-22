import tmp.sheaf.xif.paper.S823StackHaarNormalizedActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S832DFactorAbsorptionAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.S823StackHaarNormalizedActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Pure d-factor arithmetic: d*L = L iff d=1 or L=0. -/
theorem dFactor_eq_iff (d L : Real) :
    d * L = L ↔ d = 1 ∨ L = 0 := by
  constructor
  · intro h
    have hzero : (d - 1) * L = 0 := by linarith
    rcases mul_eq_zero.mp hzero with hd | hL
    · left
      linarith
    · exact Or.inr hL
  · rintro (rfl | rfl) <;> ring

/-- Multiplying by a nonzero global weight does not absorb the d factor. -/
theorem weighted_dFactor_iff (w d L : Real) (hw : w ≠ 0) :
    w * (d * L) = w * L ↔ d * L = L := by
  constructor
  · intro h
    exact mul_left_cancel₀ hw h
  · intro h
    rw [h]

/-- Exact conclusion for the S823 d factor. -/
theorem stackHaar_dFactor_absorption_iff (d : Nat) :
    StackHaarDFactorCondition (l := l) T b d ↔
      (d : Real) = 1 ∨ paperQPilotLogLeast (l := l) T b = 0 := by
  unfold StackHaarDFactorCondition
  exact dFactor_eq_iff _ _

end LeanFormal.IUT.XiFPaper.S832DFactorAbsorptionAuditActual

end
