import tmp.sheaf.xif.paper.Mzk1ThetaHullHaarConsumerGlueActual

/-! # Mzk1ThetaHullScalingConsumerGlueActual — sign/dimension consequences of the O6 law

Small glue module (no new mathematics): derives the negativity of the p-adic hull scaling
correction (hence monotonicity of the hull log-volume under scaling) from the already-proved
`thetaHull_logVolume_prime_smul_sub` and `thetaHullDimFactor_pos`.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaHullScalingConsumerGlueActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaHullHaarNormalizationActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaHullHaarConsumerGlueActual
open MeasureTheory
open scoped Pointwise ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}

/-- The scaling correction `-dim · log p` is negative for `p > 1`. -/
theorem thetaHull_scaling_correction_neg
    (C3 : SourcePilotRegionData (l := l) (V := V) I) (hp : 1 < (C3.p : Real)) :
    -(thetaHullDimFactor C3) * Real.log (C3.p : Real) < 0 := by
  have hdim : 0 < thetaHullDimFactor C3 := thetaHullDimFactor_pos C3
  have hlog : 0 < Real.log (C3.p : Real) := Real.log_pos hp
  nlinarith

/-- Scaling the hull by `p` does not increase its log-volume. -/
theorem thetaHull_logVolume_prime_smul_le
    (C3 : SourcePilotRegionData (l := l) (V := V) I) (hp : 1 < (C3.p : Real))
    (hpos : 0 < (actualC3LogShellTensorHaar C3) (thetaPilotHull C3)) :
    Real.log ((actualC3LogShellTensorHaar C3)
        ((C3.p : ℚ_[C3.p]) • thetaPilotHull C3)).toReal <=
      thetaPilotHullLogVolumeReal C3 := by
  have h := thetaHull_logVolume_prime_smul_sub C3 hpos
  have hcorr : -(thetaHullDimFactor C3) * Real.log (C3.p : Real) <= 0 :=
    le_of_lt (thetaHull_scaling_correction_neg C3 hp)
  linarith

/-- The block dimension is a positive natural number. -/
theorem c3TensorBlockDimension_pos_apply
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    0 < c3TensorBlockDimension C3 :=
  (thetaHullHaarNormalizationLaw C3).block_dim_pos

#check thetaHull_scaling_correction_neg
#check thetaHull_logVolume_prime_smul_le
#check c3TensorBlockDimension_pos_apply

end LeanFormal.IUT.XiFPaper.Mzk1ThetaHullScalingConsumerGlueActual
end
