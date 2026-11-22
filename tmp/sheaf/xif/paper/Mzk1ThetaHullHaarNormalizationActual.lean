import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual

/-! # Mzk1ThetaHullHaarNormalizationActual — O6 object: Theta-hull Haar normalization law

A499 object-construction (no wiring): packages the **actual** Theta-hull Haar normalization
law as a definition-level object, constructed from the real C3 tensor log-shell data:
* hull = the actual tensor log-shell region (lambda-O hull, S3137QThetaPilot:102);
* log-volume = log of the actual Haar measure of that region (S3137:70 / AbsTopIII09:62);
* scaling law: log Haar(p_v • hull) = -(blockDim)*log p_v + log Haar(hull) (S3137:59);
* block dimension positive (S3137C3...:58).
Every field is discharged by the existing PROVED theorems; no q/(2l) readout, no wiring,
no sorry/axiom. Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaHullHaarNormalizationActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open MeasureTheory
open scoped Pointwise ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}

/-- **O6 object:** the actual Theta-hull Haar normalization law over the C3 tensor
log-shell data: finiteness, region identification, log-volume readout, p-adic scaling
law, and positive block dimension. -/
structure ThetaHullHaarNormalizationLaw (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    Prop where
  hull_finite : (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤
  hull_eq_region : thetaPilotHull C3 = actualC3LogShellTensorRegion C3
  log_readout : thetaPilotHullLogVolumeReal C3 =
    Real.log ((actualC3LogShellTensorHaar C3) (actualC3LogShellTensorRegion C3)).toReal
  scaling_law : ∀ (_hpos : 0 < (actualC3LogShellTensorHaar C3) (thetaPilotHull C3)),
    Real.log ((actualC3LogShellTensorHaar C3)
        ((C3.p : ℚ_[C3.p]) • thetaPilotHull C3)).toReal =
      -(c3TensorBlockDimension C3 : ℝ) * Real.log (C3.p : ℝ) + thetaPilotHullLogVolumeReal C3
  block_dim_pos : 0 < c3TensorBlockDimension C3

/-- The object is constructed (not assumed) from the actual C3 data. -/
theorem thetaHullHaarNormalizationLaw
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    ThetaHullHaarNormalizationLaw C3 where
  hull_finite := thetaPilotHull_measure_lt_top (C3 := C3)
  hull_eq_region := thetaPilotHull_eq_region (C3 := C3)
  log_readout := thetaPilotHullLogVolumeReal_eq_actualRegion (C3 := C3)
  scaling_law := fun hpos => thetaPilotHull_log_measure_prime_smul (C3 := C3) hpos
  block_dim_pos := c3TensorBlockDimension_pos (C3 := C3)

/-- Consumer: the log-volume of the p_v-scaled hull in terms of the block dimension. -/
theorem thetaHull_logVolume_prime_smul
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (hpos : 0 < (actualC3LogShellTensorHaar C3) (thetaPilotHull C3)) :
    Real.log ((actualC3LogShellTensorHaar C3)
        ((C3.p : ℚ_[C3.p]) • thetaPilotHull C3)).toReal =
      -(c3TensorBlockDimension C3 : ℝ) * Real.log (C3.p : ℝ) + thetaPilotHullLogVolumeReal C3 :=
  (thetaHullHaarNormalizationLaw C3).scaling_law hpos

/-- A499 object-construction convention: the O6 object is *constructed* from the actual C3
data (not passed as a parameter). -/
theorem thetaHullHaarNormalizationLaw_constructed
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    ThetaHullHaarNormalizationLaw C3 :=
  thetaHullHaarNormalizationLaw C3

#check thetaHullHaarNormalizationLaw_constructed

#check ThetaHullHaarNormalizationLaw
#check thetaHullHaarNormalizationLaw

end LeanFormal.IUT.XiFPaper.Mzk1ThetaHullHaarNormalizationActual
end
