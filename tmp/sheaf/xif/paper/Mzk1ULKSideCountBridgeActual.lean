/- K-side count 版 D letter 到全局 logDifferentK 的无条件桥（自主任务）: 
Σ_b normDegreeWeight_b * ksDCount_b ≤ logDifferentK。 -/
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1ULKSideLettersActual
import tmp.sheaf.xif.paper.Mzk1HT82PaperWeightDiffActual
import tmp.sheaf.xif.paper.Mzk1HT82UnderIntGenQVActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULKSideCountBridgeActual

open LeanFormal.IUT
open NumberField
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open UniqueFactorizationMonoid
open scoped BigOperators

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- 坏 index 对应的 K-prime。 -/
noncomputable def badKIdeal (b : Bad (nativePlaceSelection T)) : Ideal (𝓞 (T.arithmetic.K)) :=
  (nativeBadToKPlace T b).maximalIdeal.asIdeal

/-- count 版 D letter。 -/
noncomputable def ksDCount (b : Bad (nativePlaceSelection T)) : ℝ :=
  ((normalizedFactors (differentIdeal ℤ (𝓞 (T.arithmetic.K)))).count (badKIdeal T b) : ℝ) *
    Real.log ((underIntGen (K := T.arithmetic.K) (badKIdeal T b)).natAbs : ℝ)

/-- b ↦ P_b 单射。 -/
theorem badKIdeal_injective : Function.Injective (badKIdeal T) := by
  intro b b' h
  have hplace : nativeBadToKPlace T b = nativeBadToKPlace T b' :=
    NumberField.FinitePlace.maximalIdeal_injective
      (IsDedekindDomain.HeightOneSpectrum.ext h)
  apply Subtype.ext
  show b.1 = b'.1
  rw [← nativeBadToKPlace_comap T b, hplace, nativeBadToKPlace_comap T b']

/-- **无条件主结果**: Σ_b normDegreeWeight_b · ksDCount_b ≤ logDifferentK。 -/
theorem sum_normDegreeWeight_mul_ksDCount_le :
    (∑ b : Bad (nativePlaceSelection T),
        normDegreeWeight T b * ksDCount T b) ≤
      Real.log (NumberField.rootDiscr T.arithmetic.K) := by
  classical
  let g : Ideal (𝓞 (T.arithmetic.K)) → ℝ := fun P =>
    paperDifferentWeight T.arithmetic.K P *
      ((normalizedFactors (differentIdeal ℤ (𝓞 (T.arithmetic.K)))).count P : ℝ) *
        Real.log ((underIntGen (K := T.arithmetic.K) P).natAbs : ℝ)
  have hsum : (∑ b : Bad (nativePlaceSelection T),
        normDegreeWeight T b * ksDCount T b)
      = ∑ P ∈ (Finset.univ.image (badKIdeal T)), g P := by
    rw [Finset.sum_image (s := Finset.univ) (g := badKIdeal T)
      (badKIdeal_injective T).injOn]
    apply Finset.sum_congr rfl
    intro b _
    simp only [g, ksDCount, normDegreeWeight, badKIdeal]
    ring
  have hzero : ∀ P ∈ Finset.univ.image (badKIdeal T),
      P ∉ differentPlaces (T.arithmetic.K) → g P = 0 := by
    intro P hP hnot
    have hcnt : (normalizedFactors (differentIdeal ℤ (𝓞 (T.arithmetic.K)))).count P = 0 := by
      rw [Multiset.count_eq_zero]
      intro hmem
      exact hnot (Multiset.mem_toFinset.mpr hmem)
    simp [g, hcnt]
  rw [hsum]
  calc ∑ P ∈ Finset.univ.image (badKIdeal T), g P
      = ∑ P ∈ Finset.univ.image (badKIdeal T),
          (if P ∈ differentPlaces (T.arithmetic.K) then g P else 0) := by
        apply Finset.sum_congr rfl
        intro P hP
        by_cases h : P ∈ differentPlaces (T.arithmetic.K)
        · simp [h]
        · simp [h, hzero P hP h]
    _ = ∑ P ∈ (Finset.univ.image (badKIdeal T)).filter
          (fun P => P ∈ differentPlaces (T.arithmetic.K)), g P := by
        rw [Finset.sum_filter]
    _ ≤ Real.log (NumberField.rootDiscr T.arithmetic.K) :=
        paperWeightedDeltaSum_subset_le_logDifferentK' (T.arithmetic.K)
          ((Finset.univ.image (badKIdeal T)).filter
            (fun P => P ∈ differentPlaces (T.arithmetic.K)))
          (by intro x hx; exact (Finset.mem_filter.mp hx).2)

#print axioms badKIdeal_injective
#print axioms sum_normDegreeWeight_mul_ksDCount_le

end LeanFormal.IUT.XiFPaper.Mzk1ULKSideCountBridgeActual
