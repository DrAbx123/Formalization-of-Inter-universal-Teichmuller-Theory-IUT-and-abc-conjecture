import tmp.sheaf.xif.paper.S3132ThetaFactorValueActual
import tmp.sheaf.xif.paper.S3137C3TensorBlockDimensionActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section
open MeasureTheory

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3137C3TensorBlockDimensionActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3132R1ThetaHalfBridgeActual
open LeanFormal.IUT.XiFPaper.S3132ThetaNormalizationFactorActual
open LeanFormal.IUT.XiFPaper.S3132ThetaFactorValueActual

namespace LeanFormal.IUT.XiFPaper.S3132ThetaFactorDimensionActual

universe u v uv upi umon ui

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance thetaDimMeas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance thetaDimBorel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-!
# task-41(a): dimension-one form of the label-level normalization factor

**Component, not a paper object.**  Owner: hull.  Consumer: the sharper target
`MissingCanonicalRootedThetaReadout` (task-41) and the registry residuals.

Ties the label-level factor value
(`S3132ThetaFactorValueActual`: finrank-one ⇒
`thetaNormalizationFactor = Real.log mu(O_hol).toReal`) to the actual
lattice-side tensor-block dimension
(`S3137C3TensorBlockDimensionActual`: `c3TensorBlockDimension C3 =
prod_i finrank_{Q_p} (C3LogShellFiber C3 i)`).  Concretely:

* `c3TensorBlockDimension_eq_finrank_block`: the dimension is the
  `Q_p`-finrank of the actual C3 tensor block;
* `c3TensorBlockDimension_eq_one_of_fiber_finrank_one`: local degree one at every
  tensor place gives dimension one;
* `thetaNormalizationFactor_eq_log_unitReference_of_fiber_finrank_one`: hence in
  that case the exact normalization factor is the unit-reference log-mass
  `Real.log mu(O_hol).toReal`.

This is a constructed value, not a missing datum; the remaining paper input is
the normalization choice `V(O_hol) = 0` (IUT III, Proposition 3.9, (i), p. 115;
Remark 3.9.5, (i), pp. 158-159; IUT IV, Proposition 1.4, (i)).
-/

/-- The actual C3 tensor-block dimension is the `Q_p`-finrank of the block. -/
theorem c3TensorBlockDimension_eq_finrank_block :
    c3TensorBlockDimension C3 =
      Module.finrank ℚ_[C3.p] (C3LogShellTensorBlock C3) :=
  rfl

/-- Local degree one at every tensor place gives tensor-block dimension one. -/
theorem c3TensorBlockDimension_eq_one_of_fiber_finrank_one
    (h : ∀ i : C3.tensorIndex,
      Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i) = 1) :
    c3TensorBlockDimension C3 = 1 := by
  rw [c3TensorBlockDimension_eq_prod_finrank C3]
  exact Finset.prod_eq_one (fun i _ => h i)

/-- Local degree one at every tensor place gives block finrank one. -/
theorem finrank_block_eq_one_of_fiber_finrank_one
    (h : ∀ i : C3.tensorIndex,
      Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i) = 1) :
    Module.finrank ℚ_[C3.p] (C3LogShellTensorBlock C3) = 1 := by
  rw [← c3TensorBlockDimension_eq_finrank_block C3,
    c3TensorBlockDimension_eq_one_of_fiber_finrank_one C3 h]

/-- **Dimension-one value of the exact normalization factor.**  If every C3
tensor place has local degree one, the raw-Haar / V-form normalization factor is
the unit-reference log-mass. -/
theorem thetaNormalizationFactor_eq_log_unitReference_of_fiber_finrank_one
    (h : ∀ i : C3.tensorIndex,
      Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i) = 1) :
    thetaNormalizationFactor C3 =
      Real.log ((actualC3LogShellTensorHaar C3)
        (arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple)).toReal :=
  thetaNormalizationFactor_eq_log_unitReference_of_finrank_one C3
    (finrank_block_eq_one_of_fiber_finrank_one C3 h)

#check c3TensorBlockDimension_eq_finrank_block
#check c3TensorBlockDimension_eq_one_of_fiber_finrank_one
#check thetaNormalizationFactor_eq_log_unitReference_of_fiber_finrank_one

end LeanFormal.IUT.XiFPaper.S3132ThetaFactorDimensionActual

end
