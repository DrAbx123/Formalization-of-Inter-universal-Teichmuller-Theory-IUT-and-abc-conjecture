import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks

/-!
# S3137: the actual C3 tensor-block Q_p-dimension as the product of local degrees

IUT III, Proposition 3.9, (i) (p. 115): the p_v-adic log-volume normalization
divides by the Q_p-dimension of the local packet.  For the actual C3 tensor
block this dimension is the product of the local degrees of the actual
completions at the selected tensor places (tensor product over Q_p), and it is
positive.  This file records that explicit formula, tying the C3 packet
normalization to the local log-volume normalization.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3137C3TensorBlockDimensionActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The actual C3 tensor-block Q_p-dimension is the product of the actual local
degrees at the selected tensor places (tensor product over Q_p). -/
theorem c3TensorBlockDimension_eq_prod_finrank :
    c3TensorBlockDimension C3 =
      ∏ i : C3.tensorIndex,
        Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i) := by
  unfold c3TensorBlockDimension C3LogShellTensorBlock C3LogShellFiber
  exact finrank_arithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple

/-- The actual C3 tensor-block dimension is positive: it is a product of
positive local degrees. -/
theorem c3TensorBlockDimension_pos_alt : 0 < c3TensorBlockDimension C3 := by
  rw [c3TensorBlockDimension_eq_prod_finrank C3]
  exact Finset.prod_pos (fun i _ => Module.finrank_pos)

end LeanFormal.IUT.XiFPaper.S3137C3TensorBlockDimensionActual
