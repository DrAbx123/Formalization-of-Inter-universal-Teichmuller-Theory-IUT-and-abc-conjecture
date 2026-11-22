/- U-R C2 J1 (P): K-side lower bound assembly (kurt), split from KLowerCore to
avoid stack/heartbeat crashes: uses the Core ceiling-region volumes/measure lemmas.

THIS FILE ONLY uses maxHeartbeats 1000000 (paper-level budget); RC registry.
-/
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellRamificationInertia
import tmp.sheaf.xif.paper.Mzk1URThetaKLowerCoreActual
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerBoundActual

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
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerCoreActual
open MeasureTheory

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ksBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (ksBlock T b)]

/-! ## Concrete hull lower bound (label-1 volume <= theta hull log volume) -/

/-- The ramification exponent of the K-side factor is positive. -/
theorem urLowerE_pos (b : Bad (nativePlaceSelection T)) : 0 < urLowerE (l := l) T b := by
  unfold urLowerE
  exact logShellRamificationExponent_pos
    (K := urLowerK T b) (p := (completionRationalPrime (nativeBadToKPlace T b)).val)

/-- The half root coefficient is at most every nonzero-label coefficient. -/
theorem ksRootCoeff_le_ksThetaCoeff (b : Bad (nativePlaceSelection T))
    (j : ksNonzeroLabel (l := l)) :
    actualRootCoeff (l := l) T b () ≤ ksThetaCoeff (l := l) T b j.1 () := by
  have hc : 0 ≤ actualRootCoeff (l := l) T b () := urRootCoeff_nonneg' (l := l) T b
  have hg : 1 ≤ (LeanFormal.IUT.gaussExponent (j.1).1).toNat :=
    Mzk1URThetaKSideActual.one_le_gaussExponent_toNat j.2
  have hg' : (1 : ℝ) ≤ ((LeanFormal.IUT.gaussExponent (j.1).1).toNat : ℝ) := by
    exact_mod_cast hg
  unfold ksThetaCoeff
  nlinarith

/-- The root ceiling is at most the ceiling of any nonzero label coefficient. -/
theorem urCeilC_le_ksCeilCoeff (b : Bad (nativePlaceSelection T))
    (j : ksNonzeroLabel (l := l)) :
    urCeilC (l := l) T b ≤
      ksCeilCoeff (l := l) T b (ksThetaCoeff (l := l) T b j.1 ()) := by
  have hc : actualRootCoeff (l := l) T b () ≤ ksThetaCoeff (l := l) T b j.1 () :=
    ksRootCoeff_le_ksThetaCoeff T b j
  have he : (0 : ℝ) < (urLowerE (l := l) T b : ℝ) := by
    exact_mod_cast urLowerE_pos (l := l) T b
  rw [urCeilC_eq (l := l) T b]
  unfold ksCeilCoeff ceilExp
  have hmul : actualRootCoeff (l := l) T b () * (urLowerE (l := l) T b : ℝ) ≤
      ksThetaCoeff (l := l) T b j.1 () * (urLowerE (l := l) T b : ℝ) :=
    mul_le_mul_of_nonneg_right hc he.le
  have hceil : (Int.ceil (actualRootCoeff (l := l) T b () *
      (urLowerE (l := l) T b : ℝ)) : ℝ) ≤
      (Int.ceil (ksThetaCoeff (l := l) T b j.1 () *
        (urLowerE (l := l) T b : ℝ)) : ℝ) := by
    exact_mod_cast Int.ceil_le_ceil hmul
  exact div_le_div_of_nonneg_right hceil he.le

/-- Every nonzero-label theta region lies in the label-1 ceiling region. -/
theorem ksThetaRegion_subset_ceilRegion (b : Bad (nativePlaceSelection T))
    (j : ksNonzeroLabel (l := l)) :
    ksThetaRegion (l := l) T b j.1 ⊆
      thetaTensorScaledRegion (places := ksPlaces T b) (tuple := ksTuple)
        (fun _ => urCeilC (l := l) T b) := by
  unfold ksThetaRegion thetaTensorScaledRegion
  have hcongr : arithmeticTupleFractionalLattice (ksPlaces T b) ksTuple
        (ksThetaCoeff (l := l) T b j.1) =
      arithmeticTupleFractionalLattice (ksPlaces T b) ksTuple
        (fun _ => ksCeilCoeff (l := l) T b (ksThetaCoeff (l := l) T b j.1 ())) := by
    apply Mzk1URThetaHullTensorActual.arithmeticTupleFractionalLattice_congr
    intro i
    exact ksLocal_ball_eq_ceil (l := l) T b (ksThetaCoeff (l := l) T b j.1 ())
      (mul_nonneg (Nat.cast_nonneg _) (urRootCoeff_nonneg' (l := l) T b))
  rw [hcongr]
  have hF : arithmeticTupleFractionalLattice (ksPlaces T b) ksTuple
        (fun _ => ksCeilCoeff (l := l) T b (ksThetaCoeff (l := l) T b j.1 ())) ≤
      arithmeticTupleFractionalLattice (ksPlaces T b) ksTuple
        (fun _ => urCeilC (l := l) T b) :=
    arithmeticTupleFractionalLattice_mono (ksPlaces T b) ksTuple
      (a := fun _ => urCeilC (l := l) T b)
      (b := fun _ => ksCeilCoeff (l := l) T b (ksThetaCoeff (l := l) T b j.1 ()))
      (fun i => urCeilC_le_ksCeilCoeff T b j)
  exact fun x hx =>
    Submodule.mul_le.mpr (fun a ha c hc => Submodule.mul_mem_mul (hF ha) hc) hx

/-- The theta image set lies in the ceiling region. -/
theorem ksThetaImageSet_subset_ceilRegion (b : Bad (nativePlaceSelection T)) :
    ksThetaImageSet (l := l) T b ⊆
      thetaTensorScaledRegion (places := ksPlaces T b) (tuple := ksTuple)
        (fun _ => urCeilC (l := l) T b) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨j, hxj⟩
  exact ksThetaRegion_subset_ceilRegion T b j hxj

/-- The theta hull lies in the closed ceiling region. -/
theorem ksThetaHull_subset_ceilRegion (b : Bad (nativePlaceSelection T)) :
    ksThetaHull (l := l) T b ⊆
      thetaTensorScaledRegion (places := ksPlaces T b) (tuple := ksTuple)
        (fun _ => urCeilC (l := l) T b) := by
  unfold ksThetaHull
  exact closure_minimal (ksThetaImageSet_subset_ceilRegion T b)
    (urCeilRegion_isClosed (l := l) T b)

/-- The theta hull has finite Haar mass. -/
theorem ksThetaHull_measure_lt_top (b : Bad (nativePlaceSelection T)) :
    MeasureTheory.Measure.addHaar (ksThetaHull (l := l) T b) < ⊤ :=
  (measure_mono (ksThetaHull_subset_ceilRegion T b)).trans_lt
    (urCeilRegion_measure_lt_top (l := l) T b)


/-- Monotonicity of the normalized log volume at the FIXED concrete places/tuple
(only the two sets vary) - shallow defeq, used by the lower bound. -/
theorem normLogVol_mono_local (b : Bad (nativePlaceSelection T))
    {S T' : Set (ksBlock T b)}
    (hST : S ⊆ T')
    (hSpos : 0 < (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (ksBlock T b)) S)
    (hTfin : (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (ksBlock T b)) T' < ⊤) :
    arithmeticTupleNormalizedLogVolume (ksPlaces T b) ksTuple
        (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (ksBlock T b)) S ≤
      arithmeticTupleNormalizedLogVolume (ksPlaces T b) ksTuple
        (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (ksBlock T b)) T' := by
  have hSfin : (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (ksBlock T b)) S < ⊤ :=
    lt_of_le_of_lt (measure_mono hST) hTfin
  have hlog : Real.log ((MeasureTheory.Measure.addHaar : MeasureTheory.Measure (ksBlock T b)) S).toReal ≤
      Real.log ((MeasureTheory.Measure.addHaar : MeasureTheory.Measure (ksBlock T b)) T').toReal :=
    Real.log_le_log (ENNReal.toReal_pos hSpos.ne' hSfin.ne)
      (ENNReal.toReal_mono hTfin.ne (measure_mono hST))
  unfold arithmeticTupleNormalizedLogVolume
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hlog _) (by positivity)

/-- Per-b lower bound: label-1 volume at most the theta hull log volume. -/
theorem ksThetaHullLog_lower (b : Bad (nativePlaceSelection T)) :
    -((urCeilC (l := l) T b) * Real.log
        ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ)) ≤
      arithmeticTupleNormalizedLogVolume (ksPlaces T b) ksTuple
        MeasureTheory.Measure.addHaar (ksThetaHull (l := l) T b) := by
  have hsub : (thetaTensorScaledRegion (places := ksPlaces T b) (tuple := ksTuple)
        (fun _ => urCeilC (l := l) T b) : Set (ksBlock T b)) ⊆ ksThetaHull (l := l) T b := by
    rw [← urLabelOneRegion_eq_ceilRegion (l := l) T b]
    exact ksOneLabelRegion_subset_hull (l := l) T b
  have hSpos : 0 < (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (ksBlock T b))
      (thetaTensorScaledRegion (places := ksPlaces T b) (tuple := ksTuple)
        (fun _ => urCeilC (l := l) T b) : Set (ksBlock T b)) :=
    urCeilRegion_measure_pos (l := l) T b
  have hTfin : (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (ksBlock T b))
      (ksThetaHull (l := l) T b) < ⊤ := ksThetaHull_measure_lt_top (l := l) T b
  rw [← urCeilRegion_logVolume (l := l) T b]
  exact normLogVol_mono_local (l := l) T b hsub hSpos hTfin

#print axioms ksThetaHullLog_lower
#print axioms ksThetaHull_measure_lt_top

#print axioms urOneLabelCoeff_eq
#print axioms urFracConst_eq
#print axioms urLabelOneRegion_eq_ceilRegion
#print axioms urLabelOneRegion_logVolume
#print axioms urCeilC_eq
#print axioms urCeilGenerator_norm
#print axioms urCeilRegion_logVolume

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerBoundActual
end