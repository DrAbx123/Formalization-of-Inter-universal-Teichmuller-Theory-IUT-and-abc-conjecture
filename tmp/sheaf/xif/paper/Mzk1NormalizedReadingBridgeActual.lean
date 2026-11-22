import tmp.sheaf.xif.paper.S3137C3DimensionConsumerActual
import tmp.sheaf.xif.paper.S3137PacketDimensionNormalizationActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual

/-!
# A541 consumer: dimension-normalized Theta reading vs raw paper Theta reading

Consumes the green S3137 relations between
* `c3PacketNormalizedLogVolume = log Haar / [block : Q_p]`,
* `c3TensorBlockDimension = prod_i finrank`,
* `thetaPilotHullLogVolumeReal = log Haar(hull)` (hull = actual region).

The result is the exact bridge `thetaPilotHullLogVolumeReal =
c3PacketNormalizedLogVolume * c3TensorBlockDimension` used when comparing the
raw hull log-volume with the packet-normalized global volume.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1NormalizedReadingBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3137C3TensorBlockDimensionActual
open LeanFormal.IUT.XiFPaper.S3137C3DimensionConsumerActual
open LeanFormal.IUT.XiFPaper.S3137PacketDimensionNormalizationActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open MeasureTheory

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance normReadingMeas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance normReadingBorel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- Dimension-normalized hull log-volume times the Q_p-dimension equals the raw
paper Theta-hull log-volume. -/
theorem normalizedHullVolume_mul_dim_eq_thetaReading :
    c3PacketNormalizedLogVolume C3 (actualC3LogShellTensorHaar C3)
        (thetaPilotHull C3) * (c3TensorBlockDimension C3 : Real) =
      thetaPilotHullLogVolumeReal C3 := by
  rw [thetaPilotHull_eq_region (C3 := C3)]
  rw [c3PacketNormalizedLogVolume_eq_log_div_prod_finrank C3
    (actualC3LogShellTensorHaar C3) (actualC3LogShellTensorRegion C3)]
  rw [thetaPilotHullLogVolumeReal_eq_actualRegion]
  rw [c3TensorBlockDimension_eq_prod_finrank C3]
  have hdim : (∏ i : C3.tensorIndex,
      (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i) : Real)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ =>
      Nat.cast_ne_zero.mpr (ne_of_gt (Module.finrank_pos)))
  field_simp
  push_cast
  ring

/-- Raw Theta reading is the dimension-normalized reading scaled by [block:Q_p]. -/
theorem thetaReading_eq_normalizedHullVolume_mul_dim :
    thetaPilotHullLogVolumeReal C3 =
      c3PacketNormalizedLogVolume C3 (actualC3LogShellTensorHaar C3)
        (thetaPilotHull C3) * (c3TensorBlockDimension C3 : Real) :=
  (normalizedHullVolume_mul_dim_eq_thetaReading C3).symm

end LeanFormal.IUT.XiFPaper.Mzk1NormalizedReadingBridgeActual
