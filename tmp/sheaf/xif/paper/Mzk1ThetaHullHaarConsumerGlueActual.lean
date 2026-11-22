import tmp.sheaf.xif.paper.Mzk1ThetaHullHaarNormalizationActual

/-! # Mzk1ThetaHullHaarConsumerGlueActual — consumer forms of the O6 normalization object

Small glue module (no new mathematics): consumes the constructed
`ThetaHullHaarNormalizationLaw` and re-expresses its scaling/readout fields as the
difference and dimension-factor forms used by the hull assembly.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaHullHaarConsumerGlueActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaHullHaarNormalizationActual
open MeasureTheory
open scoped Pointwise ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}

/-- The dimension factor appearing in the p-adic hull scaling law. -/
noncomputable def thetaHullDimFactor
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Real :=
  (c3TensorBlockDimension C3 : Real)

/-- The scaling law written as a difference: the correction term is exactly
`-dim · log p`. -/
theorem thetaHull_logVolume_prime_smul_sub
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (hpos : 0 < (actualC3LogShellTensorHaar C3) (thetaPilotHull C3)) :
    Real.log ((actualC3LogShellTensorHaar C3)
        ((C3.p : ℚ_[C3.p]) • thetaPilotHull C3)).toReal -
      thetaPilotHullLogVolumeReal C3 =
        -(thetaHullDimFactor C3) * Real.log (C3.p : Real) := by
  have h := (thetaHullHaarNormalizationLaw C3).scaling_law hpos
  unfold thetaHullDimFactor
  linarith

/-- The readout field: the hull log-volume is the log of the actual Haar measure. -/
theorem thetaHull_logVolume_eq_haar
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    thetaPilotHullLogVolumeReal C3 =
      Real.log ((actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3)).toReal :=
  (thetaHullHaarNormalizationLaw C3).log_readout

/-- The dimension factor is positive. -/
theorem thetaHullDimFactor_pos
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    0 < thetaHullDimFactor C3 := by
  unfold thetaHullDimFactor
  exact_mod_cast (thetaHullHaarNormalizationLaw C3).block_dim_pos

#check thetaHullDimFactor
#check thetaHull_logVolume_prime_smul_sub
#check thetaHull_logVolume_eq_haar
#check thetaHullDimFactor_pos

end LeanFormal.IUT.XiFPaper.Mzk1ThetaHullHaarConsumerGlueActual
end
