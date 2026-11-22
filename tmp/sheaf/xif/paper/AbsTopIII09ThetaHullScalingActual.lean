import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

/-!
# STEP 0 prior-art: thetaPilotHull|thetaPilotHullLogVolumeReal|c3Tensor|p-scaling -> hits S3137ThetaHullVolumeScalingActual (green): thetaPilotHull_measure_lt_top:51, thetaPilotHull_log_measure_prime_smul:59, thetaPilotHullLogVolumeReal_eq_actualRegion:70 -> REUSE (aliases only; no re-proof).

# [AbsTopIII] 09: Theta-side p_v-adic scaling of the actual hull log-volume (PROVED in tree)

Corpus: papers/motizuki_corpus/text/Topics in Absolute Anabelian Geometry III.txt.
Prop 5.7 (i)(b) 7938-7951 and Cor 5.10 (ii) 8594-8598: multiplicative/scaling
behaviour of the local log-volume.  Concrete Theta-side realization: the actual
lambda-O hull reading of the C3 tensor log-shell scales by
-[block : Q_p] * log p under multiplication by p (IUT III Prop 3.9(i)); the tree
proves this in S3137ThetaHullVolumeScalingActual.  Re-exported here; no re-proof.
-/

namespace LeanFormal.IUT.XiFPaper.AbsTopIII09ThetaHullScalingActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open MeasureTheory
open scoped Pointwise ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance absTopIIIThetaHullMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance absTopIIIThetaHullBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- Theta-side p_v-adic scaling of the actual hull log-volume (reused from
S3137ThetaHullVolumeScalingActual:59). -/
theorem absTopIII_thetaHull_log_measure_prime_smul
    (hpos : 0 < (actualC3LogShellTensorHaar C3) (thetaPilotHull C3)) :
    Real.log ((actualC3LogShellTensorHaar C3)
      ((C3.p : ℚ_[C3.p]) • thetaPilotHull C3)).toReal =
    -(c3TensorBlockDimension C3 : ℝ) * Real.log (C3.p : ℝ) +
    thetaPilotHullLogVolumeReal C3 :=
  thetaPilotHull_log_measure_prime_smul (C3 := C3) hpos

/-- The Theta-hull reading is the actual Haar log-volume of the actual tensor
log-shell region (reused from S3137ThetaHullVolumeScalingActual:70). -/
theorem absTopIII_thetaPilotHullLogVolumeReal_eq_actualRegion :
    thetaPilotHullLogVolumeReal C3 =
    Real.log ((actualC3LogShellTensorHaar C3)
      (actualC3LogShellTensorRegion C3)).toReal :=
  thetaPilotHullLogVolumeReal_eq_actualRegion (C3 := C3)

#check absTopIII_thetaHull_log_measure_prime_smul
#check absTopIII_thetaPilotHullLogVolumeReal_eq_actualRegion

end LeanFormal.IUT.XiFPaper.AbsTopIII09ThetaHullScalingActual
end