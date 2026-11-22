import tmp.sheaf.xif.paper.S3132SharperThetaTargetReductionActual
import tmp.sheaf.xif.paper.S3132ThetaFactorValueActual
import tmp.sheaf.xif.paper.S3131CanonicalRootedQCActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

noncomputable section
open MeasureTheory

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3132R1ThetaHalfBridgeActual
open LeanFormal.IUT.XiFPaper.S3132ThetaNormalizationFactorActual
open LeanFormal.IUT.XiFPaper.S3132ThetaFactorValueActual
open LeanFormal.IUT.XiFPaper.S3132SharperThetaTargetReductionActual
open LeanFormal.IUT.XiFPaper.S3132CanonicalRootedThetaTargetActual
open LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual

namespace LeanFormal.IUT.XiFPaper.S3132ThetaFactorZeroConditionActual

universe u v uv upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type} {I2 : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I2)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]

local instance thetaZeroMeas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance thetaZeroBorel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-!
# task-61: precise vanishing condition for the exact normalization factor

**Component, not a paper object.**  Owner: hull.  Consumer: the two final
Theta-half residuals (`MissingVFormCanonicalIdentification` and
`thetaNormalizationFactor = 0`) of task-41, and the registry ids
`INDEX.ThetaHalf.normalization-factor-zero`.

With `d = finrank_{Q_p}(C3LogShellTensorBlock C3)` and

    thetaNormalizationFactor C3 = log mu(hull) - (1/d)(log mu(hull) - log mu(O_hol))

(the exact value in `S3132ThetaNormalizationFactorActual`), this module proves the
**precise vanishing condition**

    thetaNormalizationFactor C3 = 0
      iff (d - 1) * log mu(hull) + log mu(O_hol) = 0,

and in the label-level (single-factor, d = 1) case

    thetaNormalizationFactor C3 = 0  iff  log mu(O_hol) = 0  (iff mu(O_hol) = 1).

Consequently the residual `thetaNormalizationFactor = 0` is NOT a free
normalization convention: at local degree one it is exactly the unit-reference
normalization `mu(O_hol) = 1` (paper `V(O_hol) = 0`, IUT III, Proposition 3.9,
(i), p. 115; Remark 3.9.5, (i), pp. 158-159; IUT IV, Proposition 1.4, (i)), and in
general it is an explicit affine mass relation.  Given the V-form/canonical
residual as well, this yields the sharper canonical target
(`MissingCanonicalRootedThetaReadout`).
-/

/-- The `Q_p`-rank of the actual C3 tensor block, as a real number. -/
def c3BlockFinrankReal : ℝ :=
  (Module.finrank ℚ_[C3.p] (C3LogShellTensorBlock C3) : ℝ)

/-- Affine form of the exact normalization factor in the actual Haar masses. -/
theorem thetaNormalizationFactor_eq_affine :
    thetaNormalizationFactor C3 =
      (1 - 1 / c3BlockFinrankReal C3) *
          Real.log ((actualC3LogShellTensorHaar C3)
            (actualHolomorphicHull C3 (actualUnitRegion C3))).toReal +
        (1 / c3BlockFinrankReal C3) *
          Real.log ((actualC3LogShellTensorHaar C3)
            (arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple)).toReal := by
  unfold thetaNormalizationFactor c3ThetaRawHaarLogVolume c3NormalizedLogVolume
    arithmeticTupleNormalizedLogVolume c3BlockFinrankReal
  field_simp
  ring

/-- **Precise vanishing condition (general rank).** -/
theorem thetaNormalizationFactor_eq_zero_iff :
    thetaNormalizationFactor C3 = 0 ↔
      (c3BlockFinrankReal C3 - 1) *
          Real.log ((actualC3LogShellTensorHaar C3)
            (actualHolomorphicHull C3 (actualUnitRegion C3))).toReal +
        Real.log ((actualC3LogShellTensorHaar C3)
          (arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple)).toReal = 0 := by
  rw [thetaNormalizationFactor_eq_affine]
  have hpos : 0 < c3BlockFinrankReal C3 := by
    unfold c3BlockFinrankReal
    exact_mod_cast Module.finrank_pos
  field_simp
  constructor <;> intro h <;> linarith

/-- **Label-level vanishing condition.**  At local degree one the exact
normalization factor vanishes exactly when the unit-reference Haar mass is one. -/
theorem thetaNormalizationFactor_eq_zero_iff_of_finrank_one
    (h1 : Module.finrank ℚ_[C3.p] (C3LogShellTensorBlock C3) = 1) :
    thetaNormalizationFactor C3 = 0 ↔
      Real.log ((actualC3LogShellTensorHaar C3)
        (arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple)).toReal = 0 := by
  rw [thetaNormalizationFactor_eq_log_unitReference_of_finrank_one C3 h1]

/-- **Residual (2) from the precise condition, and the sharper target.**  Given
the label-level unit-reference normalization `log mu(O_hol) = 0` (i.e.
`mu(O_hol) = 1`) and the V-form/canonical residual, the sharper canonical target
follows. -/
theorem missingCanonicalRootedThetaReadout_of_finrank_one_unitReference
    (h1 : Module.finrank ℚ_[C3.p] (C3LogShellTensorBlock C3) = 1)
    (hO : Real.log ((actualC3LogShellTensorHaar C3)
      (arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple)).toReal = 0)
    (hV : MissingVFormCanonicalIdentification C3 T mu) :
    MissingCanonicalRootedThetaReadout I C3 T mu :=
  MissingCanonicalRootedThetaReadout_of_factor_zero_and_VForm
    (I := I) (C3 := C3) (T := T) (mu := mu)
    ((thetaNormalizationFactor_eq_zero_iff_of_finrank_one C3 h1).mpr hO) hV

#check thetaNormalizationFactor_eq_affine
#check thetaNormalizationFactor_eq_zero_iff
#check thetaNormalizationFactor_eq_zero_iff_of_finrank_one
#check missingCanonicalRootedThetaReadout_of_finrank_one_unitReference

end LeanFormal.IUT.XiFPaper.S3132ThetaFactorZeroConditionActual

end