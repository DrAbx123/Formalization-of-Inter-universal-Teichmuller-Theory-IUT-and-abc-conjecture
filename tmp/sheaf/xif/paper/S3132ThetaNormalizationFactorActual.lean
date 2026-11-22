import tmp.sheaf.xif.paper.S3132R1ThetaHalfBridgeActual
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume

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

namespace LeanFormal.IUT.XiFPaper.S3132ThetaNormalizationFactorActual

universe u v uv upi umon ui

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance thetaNormMeas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance thetaNormBorel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-!
# task-41(a): the raw-Haar -> degree-normalized V-form channel and its exact factor

**Component, not a paper object.**  Owner: hull.  Consumer: the normalization
residual `MissingThetaLogNormalization` of the task-38 Theta-half reduction
(`S3132UniformFactorComparisonComponentActual`).

The paper's signed readout is the degree-normalized log-volume
`arithmeticTupleNormalizedLogVolume` (V-form; IUT III, Proposition 3.9, (i),
p. 115; IUT IV, Proposition 1.4, (i)):

    V(S) = (1 / finrank_{Q_p} block) * (log mu(S) - log mu(O_hol)),

with `O_hol = arithmeticTupleCanonicalUnitReference`, while the actual C3-packet
Theta reading `thetaPilotHullLogVolumeReal` is `Real.log` of the raw Haar measure
of the actual paper hull (my R1-Theta bridge
`thetaPilotHullLogVolumeReal_eq_log_actualHaar`).

This module constructs the channel `c3NormalizedLogVolume` on the actual C3
packet and exposes the **exact normalization factor** of the target identity:

    thetaPilotHullLogVolumeReal C3
      = V(actual paper hull) + thetaNormalizationFactor C3,

where `thetaNormalizationFactor C3 = log mu(hull) - V(hull)` is an actual real
number (fully expressed through the actual Haar masses of the paper hull and of
the canonical unit reference; `thetaNormalizationFactor_eq`).  The residual is
therefore reduced to two field-level statements about actual objects:
(i) the value of `thetaNormalizationFactor` (equivalently its vanishing) and
(ii) the identification of `V(actual paper hull)` with the canonical rooted
V-form readout `S3134CanonicalRootedHC T mu` (shehdd's names); no carrier
substitution and no value-layer surrogate is used.
-/

/-- The degree-normalized V-form log-volume on the actual C3 log-shell tensor
packet, applied to the actual Haar measure. -/
noncomputable def c3NormalizedLogVolume
    (S : Set (C3LogShellTensorBlock C3)) : ℝ :=
  arithmeticTupleNormalizedLogVolume C3.tensorPlaces C3.tensorTuple
    (actualC3LogShellTensorHaar C3) S

/-- The raw Haar log-volume of the actual paper hull (the R1-Theta reading
expression). -/
noncomputable def c3ThetaRawHaarLogVolume : ℝ :=
  Real.log ((actualC3LogShellTensorHaar C3
    (actualHolomorphicHull C3 (actualUnitRegion C3))).toReal)

/-- The R1-Theta reading is the raw Haar log-volume of the actual paper hull. -/
theorem thetaPilotHullLogVolumeReal_eq_c3ThetaRawHaarLogVolume :
    thetaPilotHullLogVolumeReal C3 = c3ThetaRawHaarLogVolume C3 :=
  thetaPilotHullLogVolumeReal_eq_log_actualHaar C3

/-- **The exact normalization factor** of the target identity: raw Haar
log-volume minus the degree-normalized V-form on the actual paper hull. -/
noncomputable def thetaNormalizationFactor : ℝ :=
  c3ThetaRawHaarLogVolume C3 -
    c3NormalizedLogVolume C3
      (actualHolomorphicHull C3 (actualUnitRegion C3))

/-- **Exposed form of the factor** through actual Haar masses only:
`log mu(hull) - (1/d)(log mu(hull) - log mu(O_hol))`. -/
theorem thetaNormalizationFactor_eq :
    thetaNormalizationFactor C3 =
      Real.log ((actualC3LogShellTensorHaar C3
          (actualHolomorphicHull C3 (actualUnitRegion C3))).toReal) -
        (1 / (Module.finrank ℚ_[C3.p]
            (C3LogShellTensorBlock C3) : ℝ)) *
          (Real.log ((actualC3LogShellTensorHaar C3
                (actualHolomorphicHull C3 (actualUnitRegion C3))).toReal) -
            Real.log ((actualC3LogShellTensorHaar C3
                (arithmeticTupleCanonicalUnitReference C3.tensorPlaces
                  C3.tensorTuple)).toReal)) := by
  rfl

/-- **Raw-Haar -> V-form channel (proved).**  The actual C3 Theta reading is the
degree-normalized V-form of the actual paper hull plus the exact normalization
factor. -/
theorem thetaPilotHullLogVolumeReal_eq_normalizedLogVolume_add_factor :
    thetaPilotHullLogVolumeReal C3 =
      c3NormalizedLogVolume C3
          (actualHolomorphicHull C3 (actualUnitRegion C3)) +
        thetaNormalizationFactor C3 := by
  rw [thetaPilotHullLogVolumeReal_eq_c3ThetaRawHaarLogVolume]
  unfold thetaNormalizationFactor c3ThetaRawHaarLogVolume
  ring

/-- **Vanishing of the factor is equivalent to the raw reading being the V-form
of the actual paper hull.** -/
theorem thetaNormalizationFactor_eq_zero_iff :
    thetaNormalizationFactor C3 = 0 ↔
      thetaPilotHullLogVolumeReal C3 =
        c3NormalizedLogVolume C3
          (actualHolomorphicHull C3 (actualUnitRegion C3)) := by
  constructor
  · intro h
    rw [thetaPilotHullLogVolumeReal_eq_normalizedLogVolume_add_factor, h, add_zero]
  · intro h
    have h' := thetaPilotHullLogVolumeReal_eq_normalizedLogVolume_add_factor C3
    rw [h] at h'
    have h2 : c3NormalizedLogVolume C3
          (actualHolomorphicHull C3 (actualUnitRegion C3)) + 0 =
        c3NormalizedLogVolume C3
          (actualHolomorphicHull C3 (actualUnitRegion C3)) + thetaNormalizationFactor C3 :=
      (add_zero (c3NormalizedLogVolume C3
        (actualHolomorphicHull C3 (actualUnitRegion C3)))).trans h'
    exact (add_left_cancel h2).symm

/-- **Reduction of the normalization residual to actual data.**  If the exact
normalization factor vanishes and the V-form of the actual paper hull equals the
canonical rooted V-form readout, then the raw C3 reading equals the canonical
rooted readout (the sharper paper-faithful target). -/
theorem thetaPilotHullLogVolumeReal_eq_canonical_of_factor_zero
    (hfac : thetaNormalizationFactor C3 = 0)
    {canonical : ℝ}
    (hV : c3NormalizedLogVolume C3
        (actualHolomorphicHull C3 (actualUnitRegion C3)) = canonical) :
    thetaPilotHullLogVolumeReal C3 = canonical := by
  rw [thetaNormalizationFactor_eq_zero_iff] at hfac
  rw [hfac, hV]

#check c3NormalizedLogVolume
#check thetaPilotHullLogVolumeReal_eq_normalizedLogVolume_add_factor
#check thetaNormalizationFactor_eq
#check thetaNormalizationFactor_eq_zero_iff
#check thetaPilotHullLogVolumeReal_eq_canonical_of_factor_zero

end LeanFormal.IUT.XiFPaper.S3132ThetaNormalizationFactorActual

end