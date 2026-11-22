import tmp.sheaf.xif.paper.S3047bActualParameterHscalarAttempt

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3047bActualParameterHscalarAttempt
open LeanFormal.IUT.XiFPaper.S3043LocalHaarVolumeSignActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3051HscalarCaseSplitActual

variable {l : PrimeGeFive} {V : Type*}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

theorem S3051_Q_nonneg : 0 <= S3047bQ := by
  unfold S3047bQ paperQAbsLog qNormFactor
  positivity

/-- Case CThetaPaper >= 0: V >= 0 suffices. -/
theorem S3051_hscalar_of_CTheta_nonneg
    (a b c : Nat) (hC : 0 <= S3047bCTheta a b c) :
    S3047bHscalar C3 a b c := by
  have hV : 0 <= actualC3LogShellTensorLogVolume C3 :=
    S3043_logVolume_nonneg C3
  have hQ : 0 <= S3047bQ := S3051_Q_nonneg
  have hprod : 0 <= S3047bCTheta a b c * S3047bQ := mul_nonneg hC hQ
  unfold S3047bHscalar
  linarith

/-- Case CThetaPaper < 0: hscalar is exactly the quantitative measure lower
bound `-C*Q <= V`. -/
theorem S3051_hscalar_iff_missing_of_neg
    (a b c : Nat) (hC : S3047bCTheta a b c < 0) :
    S3047bHscalar C3 a b c ↔
      S3047bMissingMeasureLowerBound C3 a b c :=
  S3047b_hscalar_iff_measureLowerBound C3 a b c

/-- In the negative case the exact required lower bound, isolated. -/
theorem S3051_required_measure_lower_bound_of_neg
    (a b c : Nat) (hC : S3047bCTheta a b c < 0) :
    S3047bHscalar C3 a b c ↔
      -S3047bCTheta a b c * S3047bQ <=
        actualC3LogShellTensorLogVolume C3 :=
  S3047b_hscalar_iff_measureLowerBound C3 a b c

#check S3051_Q_nonneg
#check S3051_hscalar_of_CTheta_nonneg
#check S3051_hscalar_iff_missing_of_neg
#check S3051_required_measure_lower_bound_of_neg
#print axioms S3051_hscalar_of_CTheta_nonneg
#print axioms S3051_hscalar_iff_missing_of_neg

end LeanFormal.IUT.XiFPaper.S3051HscalarCaseSplitActual
end
