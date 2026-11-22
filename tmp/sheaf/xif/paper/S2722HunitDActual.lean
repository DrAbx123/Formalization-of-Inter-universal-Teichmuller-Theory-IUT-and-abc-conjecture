import tmp.sheaf.xif.paper.S2720BridgeHaarActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction
import tmp.sheaf.xif.paper.S2590PadicSingletonNullActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorNontrivial
import Mathlib.MeasureTheory.Group.Measure

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2722HunitDActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
open LeanFormal.IUT.XiFPaper.S2590PadicSingletonNullActual
open LeanFormal.IUT.XiFPaper.S2720BridgeHaarActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

/-- The nonnegative additive constant measuring unitRegion log-volume above hull
log-volume for the concrete S2586 Haar interface. -/
noncomputable def S2722D0 : Real :=
  max 0
    (((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        (S2586IQHullLogVolumeInterface (l := l) T b).unitRegion).toReal -
      ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        (S2586IQHullLogVolumeInterface (l := l) T b).hull).toReal)

theorem S2722D0_nonneg : 0 ≤ S2722D0 (l := l) T b :=
  le_max_left _ _

theorem S2722_hunitD :
    (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        (S2586IQHullLogVolumeInterface (l := l) T b).unitRegion
      ≤ (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
          (S2586IQHullLogVolumeInterface (l := l) T b).hull +
        ENNReal.ofReal (S2722D0 (l := l) T b) := by
  let W := S2586IQHullLogVolumeInterface (l := l) T b
  let avol := W.logVolume W.unitRegion
  let hvol := W.logVolume W.hull
  have ha : avol ≠ ⊤ := ne_of_lt W.unitRegion_logVolume_lt_top
  have hb : hvol ≠ ⊤ := ne_of_lt W.hull_logVolume_lt_top
  have hDnonneg : 0 ≤ S2722D0 (l := l) T b := S2722D0_nonneg (l := l) T b
  have hRne : hvol + ENNReal.ofReal (S2722D0 (l := l) T b) ≠ ⊤ :=
    ne_of_lt (ENNReal.add_lt_top.mpr ⟨W.hull_logVolume_lt_top, ENNReal.ofReal_lt_top⟩)
  change avol ≤ hvol + ENNReal.ofReal (S2722D0 (l := l) T b)
  rw [← ENNReal.toReal_le_toReal ha hRne]
  rw [ENNReal.toReal_add hb ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hDnonneg]
  dsimp [S2722D0]
  have hmax : avol.toReal - hvol.toReal
      ≤ max 0 (avol.toReal - hvol.toReal) := le_max_right _ _
  linarith

/-- Gap-2 reduction with the actual nonnegative D0 (no hardcoded D0 = 0). -/
theorem S2722_gap2_with_D0
    (eps : Real)
    (hpoint : ∀ a n c : Nat, IsABCTriple a n c →
      ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        {(S2586IQHullLogVolumeInterface (l := l) T b).scaleShift
          (S2588PointMap T b a n c)}).toReal
      ≤ (1 + eps) * arithmeticWeight (abcRationalPoint a c)) :
    ∃ D : Real, ∀ a n c : Nat, IsABCTriple a n c →
      ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        (normalizedComparisonRegion
          (S2586IQHullLogVolumeInterface (l := l) T b)
          (S2588PointMap T b) a n c)).toReal
      ≤ (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
          ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
            (S2586IQHullLogVolumeInterface (l := l) T b).hull).toReal + D := by
  refine cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound
    (D₁ := 0)
    (S2586IQHullLogVolumeInterface (l := l) T b) (S2588PointMap T b)
    (S2722D0_nonneg (l := l) T b) (S2722_hunitD (l := l) T b) ?_ ?_ ?_
  · intro a n c habc
    simpa [normalizedComparisonRegion] using
      normalizedRegion_logVolume_le_split (l := l) T b
        (S2588PointMap T b) a n c
  · intro a n c habc
    haveI : Module.IsTorsionFree ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b) :=
      (Module.finBasis ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b)).isTorsionFree
    haveI : Filter.NeBot
        (nhdsWithin (0 : qVFamTensorBlock T b) {(0 : qVFamTensorBlock T b)}ᶜ) :=
      Module.punctured_nhds_neBot ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b) 0
    haveI : NullSingletonClass
        (Measure.addHaar : Measure (qVFamTensorBlock T b)) :=
      MeasureTheory.Measure.IsAddHaarMeasure.nullSingletonClass _
    show (Measure.addHaar : Measure (qVFamTensorBlock T b))
      {S2588PointMap T b a n c} < ⊤
    rw [MeasureTheory.NullSingletonClass.measure_singleton]
    exact ENNReal.zero_lt_top
  · intro a n c habc
    simpa using hpoint a n c habc

#check S2722D0
#check S2722D0_nonneg
#check S2722_hunitD
#check S2722_gap2_with_D0
#print axioms S2722_hunitD
#print axioms S2722_gap2_with_D0
end LeanFormal.IUT.XiFPaper.S2722HunitDActual
end
