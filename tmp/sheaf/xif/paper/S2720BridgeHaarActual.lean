import tmp.sheaf.xif.paper.S2586IQHullLogVolumeInstantiationActual
import tmp.sheaf.xif.paper.S2590PadicSingletonNullActual
import Mathlib.MeasureTheory.Group.Measure

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2720BridgeHaarActual

open MeasureTheory
open scoped Topology
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open LeanFormal.IUT.XiFPaper.S2590PadicSingletonNullActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

/-- For the concrete S2586 interface, the hull log-volume is bounded by the unit
region log-volume: the hull is contained in the (identity) scale-shift of the
unit region. -/
theorem hull_logVolume_le_unitRegion :
    (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        (S2586IQHullLogVolumeInterface (l := l) T b).hull
      ≤ (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
          (S2586IQHullLogVolumeInterface (l := l) T b).unitRegion := by
  apply (S2586IQHullLogVolumeInterface (l := l) T b).logVolume_mono
  intro x hx
  have h := (S2586IQHullLogVolumeInterface (l := l) T b).hull_subset_scaleShift hx
  simpa [S2586IQHullLogVolumeInterface] using h

/-- Subadditivity of the S2586 log-volume (Haar measure) on unions. -/
theorem logVolume_union_le (S U : Set (qVFamTensorBlock T b)) :
    (S2586IQHullLogVolumeInterface (l := l) T b).logVolume (S ∪ U)
      ≤ (S2586IQHullLogVolumeInterface (l := l) T b).logVolume S
        + (S2586IQHullLogVolumeInterface (l := l) T b).logVolume U := by
  change (Measure.addHaar : Measure (qVFamTensorBlock T b)) (S ∪ U)
    ≤ (Measure.addHaar : Measure (qVFamTensorBlock T b)) S
      + (Measure.addHaar : Measure (qVFamTensorBlock T b)) U
  exact measure_union_le S U

/-- Singleton log-volume finiteness for the concrete S2586 interface. -/
theorem singleton_logVolume_lt_top (x : qVFamTensorBlock T b) :
    (S2586IQHullLogVolumeInterface (l := l) T b).logVolume {x} < ⊤ := by
  haveI : Module.IsTorsionFree ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b) :=
    (Module.finBasis ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b)).isTorsionFree
  haveI : Filter.NeBot
      (nhdsWithin (0 : qVFamTensorBlock T b) {(0 : qVFamTensorBlock T b)}ᶜ) :=
    Module.punctured_nhds_neBot ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b) 0
  haveI : NullSingletonClass
      (Measure.addHaar : Measure (qVFamTensorBlock T b)) :=
    MeasureTheory.Measure.IsAddHaarMeasure.nullSingletonClass _
  have h0 : (S2586IQHullLogVolumeInterface (l := l) T b).logVolume {x} = 0 :=
    MeasureTheory.NullSingletonClass.measure_singleton x
  rw [h0]
  exact ENNReal.zero_lt_top

/-- The per-triple split used by gap 2: the normalized comparison region volume is
at most the unit-region part plus the singleton point part. -/
theorem normalizedRegion_logVolume_le_split
    (point : Nat → Nat → Nat → qVFamTensorBlock T b) (a n c : Nat) :
    (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        ((S2586IQHullLogVolumeInterface (l := l) T b).scaleShift ''
          ((S2586IQHullLogVolumeInterface (l := l) T b).unitRegion ∪ {point a n c}))
      ≤ (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
          ((S2586IQHullLogVolumeInterface (l := l) T b).scaleShift ''
            (S2586IQHullLogVolumeInterface (l := l) T b).unitRegion)
        + (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
            {(S2586IQHullLogVolumeInterface (l := l) T b).scaleShift (point a n c)} := by
  rw [show (S2586IQHullLogVolumeInterface (l := l) T b).scaleShift ''
      ((S2586IQHullLogVolumeInterface (l := l) T b).unitRegion ∪ {point a n c}) =
      ((S2586IQHullLogVolumeInterface (l := l) T b).scaleShift ''
        (S2586IQHullLogVolumeInterface (l := l) T b).unitRegion)
      ∪ {(S2586IQHullLogVolumeInterface (l := l) T b).scaleShift (point a n c)} by
    ext y
    simp only [Set.mem_image, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx | hx, rfl⟩
      · exact Or.inl ⟨x, hx, rfl⟩
      · exact Or.inr (by rw [hx])
    · rintro (⟨x, hx, rfl⟩ | rfl)
      · exact ⟨x, Or.inl hx, rfl⟩
      · exact ⟨point a n c, Or.inr rfl, rfl⟩]
  exact logVolume_union_le T b _ _

#print axioms hull_logVolume_le_unitRegion
#print axioms logVolume_union_le
#print axioms singleton_logVolume_lt_top
#print axioms normalizedRegion_logVolume_le_split

end LeanFormal.IUT.XiFPaper.S2720BridgeHaarActual
end
