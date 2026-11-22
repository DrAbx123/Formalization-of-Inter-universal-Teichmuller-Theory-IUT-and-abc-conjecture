/- K-side lower bound: shallow-defeq measure layer (kurt), split from
Mzk1URThetaKLowerBoundActual to avoid deep defeq whnf timeouts.

places/tuple are FIXED (ksPlaces T b, ksTuple); only the two sets {S T : Set (ksBlock T b)} are
abstract, so unification stays shallow. Provides the measure facts and the normalized-log
monotonicity used by ksThetaHullLog_lower.

Default heartbeats (2M only in the parent Bound file).
-/
import tmp.sheaf.xif.paper.Mzk1URThetaKLowerCoreActual
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import tmp.sheaf.xif.paper.Mzk1URThetaKLowerCoreActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerBoundMeasureActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaHullTensorActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaHullUpperActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaHullNonzeroActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerCoreActual
open MeasureTheory

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ksBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (ksBlock T b)]

/-- The theta hull lies in the closed ceiling region (moved here from Bound). -/
theorem ksThetaHull_subset_ceilRegion (b : Bad (nativePlaceSelection T)) :
    ksThetaHull (l := l) T b ⊆
      thetaTensorScaledRegion (places := ksPlaces T b) (tuple := ksTuple)
        (fun _ => urCeilC (l := l) T b) := by
  unfold ksThetaHull
  exact closure_minimal (ksThetaImageSet_subset_ceilRegion T b)
    (urCeilRegion_isClosed (l := l) T b)

/-- The theta hull has finite Haar mass (moved here from Bound). -/
theorem ksThetaHull_measure_lt_top (b : Bad (nativePlaceSelection T)) :
    MeasureTheory.Measure.addHaar (ksThetaHull (l := l) T b) < ⊤ :=
  (measure_mono (ksThetaHull_subset_ceilRegion (l := l) T b)).trans_lt
    (urCeilRegion_measure_lt_top (l := l) T b)

/-- Normalized-log monotonicity at the FIXED concrete places/tuple, only the sets varying. -/
theorem normLogVol_mono_local {S T' : Set (ksBlock T b)}
    (hST : S ⊆ T')
    (hSpos : 0 < (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (ksBlock T b)) S)
    (hTfin : (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (ksBlock T b)) T' < ⊤) :
    arithmeticTupleNormalizedLogVolume (ksPlaces T b) ksTuple
        (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (ksBlock T b)) S ≤
      arithmeticTupleNormalizedLogVolume (ksPlaces T b) ksTuple
        (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (ksBlock T b)) T' := by
  have hDpos : (0 : ℝ) < (Module.finrank ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val]
      (ksBlock T b) : ℝ) := by
    exact_mod_cast finrank_arithmeticTensorTupleBlock_pos (ksPlaces T b) ksTuple
  have hSfin : (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (ksBlock T b)) S < ⊤ :=
    lt_of_le_of_lt (measure_mono hST) hTfin
  have hlog : Real.log ((MeasureTheory.Measure.addHaar : MeasureTheory.Measure (ksBlock T b)) S).toReal ≤
      Real.log ((MeasureTheory.Measure.addHaar : MeasureTheory.Measure (ksBlock T b)) T').toReal :=
    Real.log_le_log (ENNReal.toReal_pos hSpos.ne' hSfin.ne)
      (ENNReal.toReal_mono hTfin.ne (measure_mono hST))
  have hinv : 0 ≤ 1 / (Module.finrank ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val]
      (ksBlock T b) : ℝ) := by positivity
  unfold arithmeticTupleNormalizedLogVolume
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hlog _) hinv

#print axioms ksThetaHull_subset_ceilRegion
#print axioms ksThetaHull_measure_lt_top
#print axioms normLogVol_mono_local

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerBoundMeasureActual
end