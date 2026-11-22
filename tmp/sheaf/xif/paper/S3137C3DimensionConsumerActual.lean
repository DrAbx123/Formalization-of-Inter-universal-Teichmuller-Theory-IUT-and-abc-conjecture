import tmp.sheaf.xif.paper.S3137PacketDimensionNormalizationActual
import tmp.sheaf.xif.paper.C3LogShellTensorHolomorphicHullActual

/-!
# S3137: normalized log-volume of the actual C3 log-shell region via local degrees

Consumer: hull/C3 Theta-half normalization use (IUT III, Prop. 3.9, (i),
p. 115).  Instance of the packet dimension formula at the actual C3 log-shell
tensor region: the normalized log-volume of the actual region is the raw Haar
log-volume of that actual region divided by the product of the actual local
degrees at the selected tensor places.  No inequality, no carrier.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3137C3DimensionConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3137C3TensorBlockDimensionActual
open LeanFormal.IUT.XiFPaper.S3137PacketDimensionNormalizationActual
open MeasureTheory

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance c3DimConsMeas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance c3DimConsBorel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- Normalized log-volume of the actual C3 unit region via the actual local
degrees. -/
theorem c3PacketNormalizedLogVolume_actualUnitRegion_eq :
    c3PacketNormalizedLogVolume C3 (actualC3LogShellTensorHaar C3)
        (actualUnitRegion C3) =
      Real.log ((actualC3LogShellTensorHaar C3 (actualUnitRegion C3)).toReal) /
        (∏ i : C3.tensorIndex,
          (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i) : ℝ)) :=
  c3PacketNormalizedLogVolume_eq_log_div_prod_finrank C3
    (actualC3LogShellTensorHaar C3) (actualUnitRegion C3)

/-- The same for the actual paper hull (the actual unit region): the normalized
log-volume of the paper hull is its raw Haar log-volume divided by the product
of actual local degrees. -/
theorem c3PacketNormalizedLogVolume_actualPaperHull_eq :
    c3PacketNormalizedLogVolume C3 (actualC3LogShellTensorHaar C3)
        (actualHolomorphicHull C3 (actualUnitRegion C3)) =
      Real.log ((actualC3LogShellTensorHaar C3
          (actualHolomorphicHull C3 (actualUnitRegion C3))).toReal) /
        (∏ i : C3.tensorIndex,
          (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i) : ℝ)) := by
  rw [actualHolomorphicHull_unitRegion_eq C3]
  exact c3PacketNormalizedLogVolume_eq_log_div_prod_finrank C3
    (actualC3LogShellTensorHaar C3) (actualUnitRegion C3)

end LeanFormal.IUT.XiFPaper.S3137C3DimensionConsumerActual