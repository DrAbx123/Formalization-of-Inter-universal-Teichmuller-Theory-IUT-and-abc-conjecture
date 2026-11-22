import tmp.sheaf.xif.paper.S3132ThetaNormalizationFactorActual

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
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3132R1ThetaHalfBridgeActual
open LeanFormal.IUT.XiFPaper.S3132ThetaNormalizationFactorActual

namespace LeanFormal.IUT.XiFPaper.S3132ThetaFactorValueActual

universe u v uv upi umon ui

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance thetaFactorMeas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance thetaFactorBorel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-!
# task-41(a) label-level value of the exact normalization factor

**Component, not a paper object.**  Owner: hull.  Consumer: the sharper target
`MissingCanonicalRootedThetaReadout` (task-41) and the dependency-order note.

In the single-tensor-factor (label) case `finrank_{Q_p}(block) = 1` the
degree-normalized V-form collapses to

    V(S) = log mu(S) - log mu(O_hol),

so the exact normalization factor of the raw C3 Theta reading
(`thetaPilotHullLogVolumeReal = Real.log mu(hull)`) is the unit-reference
log-mass:

    thetaNormalizationFactor C3
      = Real.log (mu (O_hol)).toReal.

This is a *constructed* value (no missing datum): the residual of the sharper
target in this case is exactly the unit-reference normalization mass, and the
paper input `0 = log mu(O_hol)` (`V(O_hol) = 0`,
`arithmeticTupleNormalizedLogVolume_canonicalUnitReference`) is the
normalization choice of IUT III, Proposition 3.9, (i), p. 115.
Pages: III Prop 3.9(i) p.115; Rem 3.9.5(i) pp.158-159; IV Prop 1.4(i).
-/

/-- **Label-level value of the exact normalization factor.**  If the C3 tensor
block has `Q_p`-rank one, the raw-Haar / V-form normalization factor is the
logarithm of the unit-reference Haar mass. -/
theorem thetaNormalizationFactor_eq_log_unitReference_of_finrank_one
    (h1 : Module.finrank ℚ_[C3.p] (C3LogShellTensorBlock C3) = 1) :
    thetaNormalizationFactor C3 =
      Real.log ((actualC3LogShellTensorHaar C3)
        (arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple)).toReal := by
  unfold thetaNormalizationFactor c3ThetaRawHaarLogVolume c3NormalizedLogVolume
  unfold arithmeticTupleNormalizedLogVolume
  rw [h1]
  norm_num

/-- **Label-level V-form value.**  In the same case the V-form of the actual
paper hull is the raw Haar log-volume minus the unit-reference log-mass. -/
theorem c3NormalizedLogVolume_eq_log_sub_of_finrank_one
    (h1 : Module.finrank ℚ_[C3.p] (C3LogShellTensorBlock C3) = 1) :
    c3NormalizedLogVolume C3
        (actualHolomorphicHull C3 (actualUnitRegion C3)) =
      Real.log ((actualC3LogShellTensorHaar C3)
          (actualHolomorphicHull C3 (actualUnitRegion C3))).toReal -
        Real.log ((actualC3LogShellTensorHaar C3)
          (arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple)).toReal := by
  unfold c3NormalizedLogVolume arithmeticTupleNormalizedLogVolume
  rw [h1]
  norm_num

#check thetaNormalizationFactor_eq_log_unitReference_of_finrank_one
#check c3NormalizedLogVolume_eq_log_sub_of_finrank_one

end LeanFormal.IUT.XiFPaper.S3132ThetaFactorValueActual

end