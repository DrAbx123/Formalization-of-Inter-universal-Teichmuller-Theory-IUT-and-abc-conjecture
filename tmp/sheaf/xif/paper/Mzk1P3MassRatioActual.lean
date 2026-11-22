import tmp.sheaf.xif.paper.Mzk1P3MassLambdaQhatActual
/-! P3 (R3.7): the native mass ratio equals the P2 `lambda/qhat` ratio iff the
blockwise native mass identification holds. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P3MassRatioActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P3MassIdentificationActual
open LeanFormal.IUT.XiFPaper.Mzk1P3MassLambdaQhatActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
theorem nativeMassL_pos (b : Bad (nativePlaceSelection T)) : 0 < nativeMassL T b :=
  Real.exp_pos _
theorem nativeMassQ_pos (b : Bad (nativePlaceSelection T)) : 0 < nativeMassQ T b :=
  Real.exp_pos _
theorem lambdaMass_pos (b : Bad (nativePlaceSelection T)) : 0 < lambdaMass T b :=
  Real.exp_pos _
theorem qhatMass_pos (b : Bad (nativePlaceSelection T)) : 0 < qhatMass T b :=
  Real.exp_pos _
/-- Ratio form of the native block identification. -/
theorem nativeMassRatio_eq_lambdaQhatRatio_iff
    (b : Bad (nativePlaceSelection T)) :
    nativeMassL T b / nativeMassQ T b = lambdaMass T b / qhatMass T b ↔
      R37R13NativeMassIdentification T b := by
  have hL : 0 < nativeMassL T b := nativeMassL_pos T b
  have hQ : 0 < nativeMassQ T b := nativeMassQ_pos T b
  have hl : 0 < lambdaMass T b := lambdaMass_pos T b
  have hq : 0 < qhatMass T b := qhatMass_pos T b
  constructor
  · intro h
    have hlog := congrArg Real.log h
    rw [Real.log_div hL.ne' hQ.ne', Real.log_div hl.ne' hq.ne'] at hlog
    rw [log_nativeMassL, log_nativeMassQ, log_lambdaMass, log_qhatMass] at hlog
    unfold R37R13NativeMassIdentification
    exact hlog
  · intro h
    apply Real.log_injOn_pos
    · exact div_pos hL hQ
    · exact div_pos hl hq
    rw [Real.log_div hL.ne' hQ.ne', Real.log_div hl.ne' hq.ne']
    rw [log_nativeMassL, log_nativeMassQ, log_lambdaMass, log_qhatMass]
    unfold R37R13NativeMassIdentification at h
    exact h
end LeanFormal.IUT.XiFPaper.Mzk1P3MassRatioActual
end