import tmp.sheaf.xif.paper.S3137C3TensorBlockDimensionActual
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual

/-!
# S3137: packet-normalized log-volume through the local-degree product

Consumer: C3 packet normalization / log-volume comparisons (IUT III Prop 3.9(i),
p. 115).  The C3 packet normalized log-volume is the raw Haar log-volume
divided by the Q_p-dimension of the actual tensor block; that dimension is the
product of the actual local degrees at the selected tensor places
(c3TensorBlockDimension_eq_prod_finrank).  This file records the combined
normalization formula on actual objects.  No inequality, no carrier.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3137PacketDimensionNormalizationActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3137C3TensorBlockDimensionActual
open MeasureTheory

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance packetDimMeas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance packetDimBorel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- The actual C3 packet normalized log-volume is the raw Haar log-volume divided
by the product of the actual local degrees at the selected tensor places. -/
theorem c3PacketNormalizedLogVolume_eq_log_div_prod_finrank
    (μ : Measure (C3LogShellTensorBlock C3)) (S : Set (C3LogShellTensorBlock C3)) :
    c3PacketNormalizedLogVolume C3 μ S =
      Real.log (μ S).toReal /
        (∏ i : C3.tensorIndex,
          (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i) : ℝ)) := by
  unfold c3PacketNormalizedLogVolume
  rw [c3TensorBlockDimension_eq_prod_finrank C3]
  push_cast
  ring

/-- The same formula with the product of local degrees shown to be positive, so
the normalization denominator is nonzero. -/
theorem c3PacketNormalizedLogVolume_eq_log_div_prod_finrank_pos
    (μ : Measure (C3LogShellTensorBlock C3)) (S : Set (C3LogShellTensorBlock C3))
    (hpos : 0 < ∏ i : C3.tensorIndex,
      (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i) : ℝ)) :
    c3PacketNormalizedLogVolume C3 μ S =
      Real.log (μ S).toReal /
        (∏ i : C3.tensorIndex,
          (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i) : ℝ)) := by
  rw [c3PacketNormalizedLogVolume_eq_log_div_prod_finrank C3]

end LeanFormal.IUT.XiFPaper.S3137PacketDimensionNormalizationActual
