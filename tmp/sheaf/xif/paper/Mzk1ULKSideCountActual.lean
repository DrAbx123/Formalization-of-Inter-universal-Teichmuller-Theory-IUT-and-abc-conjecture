/-
U-C (P): the D letter, count version (paper IUT IV Def 1.9 L1236-1251; Thm 1.10
L1045-1102: log(dF_v) := deg_{V(F)_v}(dF^ADiv), normalized E-degree L977-1000).
The Step(viii) D letter is the fiber-normalized different degree: full count
delta_P times log p_P, weighted by normDegreeWeight = f_P/[K:Q].  The log-shell
normalized paperOrder delta/e belongs to the accepted StepV volume bound d_I
slot (accepted L814 internals), not to this D slot.

This file defines the count-version D letter and proves
    sum_b normDegreeWeight b * ksDCount b <= logDifferentK
unconditionally; the p-alignment bridge (underIntGen P_b).natAbs = qVFamTensorP T b is
supplied by david's Mzk1HT82UnderIntGenQVActual.underIntGen_natAbs_eq_qVFamTensorP' (20:33:18).
-/
import tmp.sheaf.xif.paper.Mzk1ULKSideLettersActual
import tmp.sheaf.xif.paper.Mzk1HT82PaperWeightDiffActual
import tmp.sheaf.xif.paper.Mzk1HT82AbsDifferentSumActual
import tmp.sheaf.xif.paper.Mzk1HT82UnderIntGenQVActual
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULKSideCountActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual
open NumberField
open UniqueFactorizationMonoid

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- the K-side place ideal attached to a bad place. -/
noncomputable def ksIdeal (b : Bad (nativePlaceSelection T)) :
    Ideal (NumberField.RingOfIntegers T.arithmetic.K) :=
  (nativeBadToKPlace T b).maximalIdeal.asIdeal

/-- D letter (count version): delta_{P_b} * log p_b with delta = count in the
global different ideal (full exponent). -/
noncomputable def ksDCount (b : Bad (nativePlaceSelection T)) : ℝ :=
  ((UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ (NumberField.RingOfIntegers T.arithmetic.K))).count (ksIdeal T b) : ℝ) * Real.log ((qVFamTensorP T b : ℕ) : ℝ)

theorem ksDCount_nonneg (b : Bad (nativePlaceSelection T)) : 0 ≤ ksDCount T b := by
  unfold ksDCount
  have h1 : (0 : ℝ) ≤ ((UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ (NumberField.RingOfIntegers T.arithmetic.K))).count (ksIdeal T b) : ℝ) := Nat.cast_nonneg _
  have h2 : 0 ≤ Real.log ((qVFamTensorP T b : ℕ) : ℝ) := by
    apply Real.log_nonneg
    have hp : Nat.Prime (qVFamTensorP T b) := (qVFamTensorPFact T b).out
    exact_mod_cast hp.one_lt.le
  exact mul_nonneg h1 h2

theorem ksDCount_eq_zero_iff (b : Bad (nativePlaceSelection T)) :
    ksDCount T b = 0 ↔ (UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ (NumberField.RingOfIntegers T.arithmetic.K))).count (ksIdeal T b) = 0 := by
  have hlog : Real.log ((qVFamTensorP T b : ℕ) : ℝ) ≠ 0 := by
    have hp : Nat.Prime (qVFamTensorP T b) := (qVFamTensorPFact T b).out
    have h1 : (1 : ℝ) < (qVFamTensorP T b : ℝ) := by exact_mod_cast hp.one_lt
    exact ne_of_gt (Real.log_pos h1)
  constructor
  · intro h
    unfold ksDCount at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact_mod_cast h'
    · exact absurd h' hlog
  · intro h
    unfold ksDCount
    rw [h]
    simp

/-- Weighted count-version D-letter aggregate bound, conditional on the single
p-alignment bridge (underIntGen P_b).natAbs = qVFamTensorP T b (TEMPORARY HOLE). -/
theorem sum_weighted_ksDCount_le_logDifferentK :
    (Finset.univ.sum (fun b : Bad (nativePlaceSelection T) => normDegreeWeight T b * ksDCount T b)) ≤
      Real.log (NumberField.rootDiscr T.arithmetic.K) := by
  classical
  let s : Finset (Bad (nativePlaceSelection T)) :=
    Finset.univ.filter (fun b => (UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ (NumberField.RingOfIntegers T.arithmetic.K))).count (ksIdeal T b) ≠ 0)
  have hzero : ∀ b : Bad (nativePlaceSelection T), b ∉ s →
      normDegreeWeight T b * ksDCount T b = 0 := by
    intro b hb
    have hc : (UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ (NumberField.RingOfIntegers T.arithmetic.K))).count (ksIdeal T b) = 0 := by
      by_contra hne
      exact hb (by
        show b ∈ Finset.univ.filter (fun b => (UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ (NumberField.RingOfIntegers T.arithmetic.K))).count (ksIdeal T b) ≠ 0)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ b, hne⟩)
    rw [(ksDCount_eq_zero_iff T b).mpr hc, mul_zero]
  have hsum1 : (Finset.univ.sum (fun b : Bad (nativePlaceSelection T) => normDegreeWeight T b * ksDCount T b))
      = s.sum (fun b => normDegreeWeight T b * ksDCount T b) := by
    have h := Finset.sum_subset (f := fun b : Bad (nativePlaceSelection T) => normDegreeWeight T b * ksDCount T b)
      (Finset.subset_univ s) (fun b _ hb => hzero b hb)
    exact h.symm
  have hterm : ∀ b : Bad (nativePlaceSelection T),
      normDegreeWeight T b * ksDCount T b =
        paperDifferentWeight T.arithmetic.K (ksIdeal T b) *
          ((UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ (NumberField.RingOfIntegers T.arithmetic.K))).count (ksIdeal T b) : ℝ) *
            Real.log (((underIntGen (K := T.arithmetic.K) (ksIdeal T b)).natAbs : ℕ) : ℝ) := by
    intro b
    have hp : qVFamTensorP T b = (underIntGen (K := T.arithmetic.K) (ksIdeal T b)).natAbs :=
      (Mzk1HT82UnderIntGenQVActual.underIntGen_natAbs_eq_qVFamTensorP' T b).symm
    unfold normDegreeWeight ksDCount
    rw [hp]
    simp only [ksIdeal]
    ring
  have hinj : Function.Injective (ksIdeal T) := by
    intro x y hxy
    have hspec : (nativeBadToKPlace T x).maximalIdeal = (nativeBadToKPlace T y).maximalIdeal :=
      IsDedekindDomain.HeightOneSpectrum.ext hxy
    have hpl : nativeBadToKPlace T x = nativeBadToKPlace T y := by
      have h := congrArg (fun v => NumberField.FinitePlace.mk v) hspec
      simpa using h
    have hcomap := congrArg (NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod)) hpl
    rw [nativeBadToKPlace_comap, nativeBadToKPlace_comap] at hcomap
    exact Subtype.ext hcomap
  have hsum2 : s.sum (fun b => normDegreeWeight T b * ksDCount T b)
      = (s.image (ksIdeal T)).sum (fun P =>
        paperDifferentWeight T.arithmetic.K P *
          ((UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ (NumberField.RingOfIntegers T.arithmetic.K))).count P : ℝ) *
            Real.log (((underIntGen (K := T.arithmetic.K) P).natAbs : ℕ) : ℝ)) := by
    rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    exact Finset.sum_congr rfl (fun b _ => hterm b)
  calc (Finset.univ.sum (fun b : Bad (nativePlaceSelection T) => normDegreeWeight T b * ksDCount T b))
      = s.sum (fun b => normDegreeWeight T b * ksDCount T b) := hsum1
    _ = (s.image (ksIdeal T)).sum (fun P =>
        paperDifferentWeight T.arithmetic.K P *
          ((UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ (NumberField.RingOfIntegers T.arithmetic.K))).count P : ℝ) *
            Real.log (((underIntGen (K := T.arithmetic.K) P).natAbs : ℕ) : ℝ)) := hsum2
    _ ≤ Real.log (NumberField.rootDiscr T.arithmetic.K) := by
        apply paperWeightedDeltaSum_subset_le_logDifferentK'
        intro P hP
        rcases Finset.mem_image.mp hP with ⟨b, hb, rfl⟩
        have hc : 0 < (UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ (NumberField.RingOfIntegers T.arithmetic.K))).count (ksIdeal T b) := by
          have hb' : b ∈ s := hb
          have hne : (UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ (NumberField.RingOfIntegers T.arithmetic.K))).count (ksIdeal T b) ≠ 0 := by
            have hmem : b ∈ Finset.univ.filter (fun b => (UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ (NumberField.RingOfIntegers T.arithmetic.K))).count (ksIdeal T b) ≠ 0) := hb'
            exact (Finset.mem_filter.mp hmem).2
          exact Nat.pos_of_ne_zero hne
        exact mem_differentPlaces_of_count_pos (K := T.arithmetic.K) hc

#print axioms ksDCount_nonneg
#print axioms ksDCount_eq_zero_iff
#print axioms sum_weighted_ksDCount_le_logDifferentK

end LeanFormal.IUT.XiFPaper.Mzk1ULKSideCountActual
end
