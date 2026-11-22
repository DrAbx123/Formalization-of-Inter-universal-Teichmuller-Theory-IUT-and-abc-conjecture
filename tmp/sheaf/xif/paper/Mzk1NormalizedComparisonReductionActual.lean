/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ProcessionNormalizedHullVolumeActual

/-!
# A526 normalized comparison reduction (fixed-constant form)

Reduction of the normalized S3137 comparison
`qPilotLogVolume ≤ thetaPilotHullLogVolumeNorm` to an inequality between the paper q
reading and the unnormalized Haar log-volume minus the FIXED reference constant
`log (haar unit region)`:

  q ≤ thetaNorm  ↔  q * [block : Q_p] ≤ log(haar hull) - log(haar unit).

No same-region identity is used: the reference is the actual UNIT region, so the fixed
constant is the normalization choice of the paper's procession-normalized log-volume.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1NormalizedComparisonReductionActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1ProcessionNormalizedHullVolumeActual
open MeasureTheory
open scoped Pointwise ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance reduceBlockMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance reduceBlockBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- The normalized hull reading as the dimension-divided ratio (from the A526 file). -/
theorem thetaNorm_eq_ratio_div
    (hH : 0 < (actualC3LogShellTensorHaar C3) (thetaPilotHull C3))
    (hR : 0 < (actualC3LogShellTensorHaar C3) (normalizationReference C3)) :
    thetaPilotHullLogVolumeNorm C3 =
      Real.log (((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal /
        ((actualC3LogShellTensorHaar C3) (normalizationReference C3)).toReal) /
        (c3TensorBlockDimension C3 : ℝ) :=
  thetaPilotHullLogVolumeNorm_eq_log_div C3 hH hR

/-- **Reduction with the fixed normalization constant**: the normalized comparison is
  equivalent to `q * dim <= log(haar hull) - log(haar unit)`. -/
theorem qThetaComparisonNorm_iff_scaled
    (hH : 0 < (actualC3LogShellTensorHaar C3) (thetaPilotHull C3))
    (hR : 0 < (actualC3LogShellTensorHaar C3) (normalizationReference C3)) :
    qThetaComparisonNorm C3 P ↔
      qPilotLogVolume C3 P * (c3TensorBlockDimension C3 : ℝ) ≤=
        thetaPilotHullLogVolumeReal C3 -
          Real.log ((actualC3LogShellTensorHaar C3)
            (normalizationReference C3)).toReal := by
  have hdim_pos : (0 : ℝ) < (c3TensorBlockDimension C3 : ℝ) :=
    Nat.cast_pos.mpr (c3TensorBlockDimension_pos (C3 := C3))
  have hdim_ne : (c3TensorBlockDimension C3 : ℝ) ≠ 0 := ne_of_gt hdim_pos
  have hratio : thetaPilotHullLogVolumeNorm C3 =
      (thetaPilotHullLogVolumeReal C3 -
        Real.log ((actualC3LogShellTensorHaar C3)
          (normalizationReference C3)).toReal) / (c3TensorBlockDimension C3 : ℝ) := by
    rw [thetaNorm_eq_ratio_div C3 hH hR]
    unfold thetaPilotHullLogVolumeReal
    rw [Real.log_div (ne_of_gt hH) (ne_of_gt hR)]
  unfold qThetaComparisonNorm
  rw [hratio, le_div_iff₀ hdim_pos]

/-- **Named candidate form**: the normalized comparison is the S3137 candidate with the
  fixed reference constant moved to the q side. -/
theorem qThetaComparisonNorm_iff_shiftedCandidate
    (hH : 0 < (actualC3LogShellTensorHaar C3) (thetaPilotHull C3))
    (hR : 0 < (actualC3LogShellTensorHaar C3) (normalizationReference C3)) :
    qThetaComparisonNorm C3 P ↔
      qPilotLogVolume C3 P * (c3TensorBlockDimension C3 : ℝ) +
          Real.log ((actualC3LogShellTensorHaar C3)
            (normalizationReference C3)).toReal ≤ thetaPilotHullLogVolumeReal C3 :=
  (qThetaComparisonNorm_iff_scaled C3 P hH hR).trans (by constructor <;> intro h <;> linarith)

end

end LeanFormal.IUT.XiFPaper.Mzk1NormalizedComparisonReductionActual