/- H-T §8.4 (A) K-side paper weights: logDifferentK = Σ_P (f_P/[K:Q])·δ_P·log p_P。

用已证:
* log_rootDiscr_eq_delta_sum（Mzk1HT82AbsDifferentSumActual）: log rootDiscr K = (1/[K:Q])·Σ δ_P log|N(P)|;
* log_absNorm_eq_inertiaDeg_mul_log_natAbs: log|N(P)| = f_P · log p（P LiesOver span {p}）。
paperWeight_b := f_P/[K:Q]；D_b := δ_P·log p。 -/
import Mathlib.Tactic
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import tmp.sheaf.xif.paper.Mzk1HT82AbsDifferentSumActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual

open NumberField UniqueFactorizationMonoid
open scoped BigOperators

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- K-side paper 权: f_P/[K:Q]（绝对 inertia degree over Q）。 -/
noncomputable def paperDifferentWeight (P : Ideal (𝓞 K)) : ℝ :=
  (P.inertiaDeg ℤ : ℝ) / (Module.finrank ℚ K : ℝ)

/-- **K-side paper-weighted δ-sum 恒等**:
Σ_{P∈differentPlaces} (f_P/[K:Q])·δ_P·log p_P = logDifferentK（= log rootDiscr K）。
pOf/hover 给出每个 P 的 underlying rational prime（ℤ base; 存在性由 ℤ PID 给出，下一批可
Classical 构造 underGenerator 消掉该参数）。 -/
theorem paperWeightedDeltaSum_eq_logDifferentK
    (pOf : Ideal (𝓞 K) → ℤ)
    (hover : ∀ P : Ideal (𝓞 K), P.IsPrime → P.LiesOver (Ideal.span {pOf P})) :
    (∑ P ∈ LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual.differentPlaces K,
        paperDifferentWeight K P *
          ((normalizedFactors (differentIdeal ℤ (𝓞 K))).count P : ℝ) *
            Real.log ((pOf P).natAbs : ℝ)) =
      Real.log (NumberField.rootDiscr K) := by
  classical
  have hI : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  rw [LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual.log_rootDiscr_eq_delta_sum K]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  have hmem : P ∈ normalizedFactors (differentIdeal ℤ (𝓞 K)) :=
    Multiset.mem_toFinset.mp hP
  obtain ⟨hprime, hle⟩ := (Ideal.mem_normalizedFactors_iff hI).mp hmem
  have hPne : P ≠ ⊥ := by
    intro hbot
    rw [hbot] at hle
    exact hI (le_bot_iff.mp hle)
  haveI : P.LiesOver (Ideal.span {pOf P}) := hover P hprime
  rw [LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual.log_absNorm_eq_inertiaDeg_mul_log_natAbs
    (K := K) (P := P) (p := pOf P)]
  unfold paperDifferentWeight
  field_simp
  try ring


/-- **子集版**: 若 S ⊆ differentPlaces K，则 Σ_{P∈S} (f_P/[K:Q])·δ_P·log p_P ≤ logDifferentK
（单调 + 各项非负; pOf/hover 参数同恒等式）。 -/
theorem paperWeightedDeltaSum_subset_le_logDifferentK
    (pOf : Ideal (𝓞 K) → ℤ)
    (hover : ∀ P : Ideal (𝓞 K), P.IsPrime → P.LiesOver (Ideal.span {pOf P}))
    (S : Finset (Ideal (𝓞 K)))
    (hS : S ⊆ LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual.differentPlaces K) :
    (∑ P ∈ S,
        paperDifferentWeight K P *
          ((normalizedFactors (differentIdeal ℤ (𝓞 K))).count P : ℝ) *
            Real.log ((pOf P).natAbs : ℝ)) ≤
      Real.log (NumberField.rootDiscr K) := by
  classical
  have hI : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  rw [← paperWeightedDeltaSum_eq_logDifferentK K pOf hover]
  apply Finset.sum_le_sum_of_subset_of_nonneg hS
  intro P hP hPnot
  have hmem : P ∈ normalizedFactors (differentIdeal ℤ (𝓞 K)) :=
    Multiset.mem_toFinset.mp hP
  obtain ⟨hprime, hle⟩ := (Ideal.mem_normalizedFactors_iff hI).mp hmem
  have hPne : P ≠ ⊥ := by
    intro hbot
    rw [hbot] at hle
    exact hI (le_bot_iff.mp hle)
  have hpne : pOf P ≠ 0 := by
    haveI : P.LiesOver (Ideal.span {pOf P}) := hover P hprime
    intro h0
    have hunder : P.under ℤ = (⊥ : Ideal ℤ) := by
      have hoverP : P.under ℤ = Ideal.span {pOf P} :=
        (Ideal.LiesOver.over (p := Ideal.span {pOf P}) (P := P)).symm
      rw [hoverP, h0]
      simp
    exact (Ideal.under_ne_bot (A := ℤ) (P := P) hPne) hunder
  have hfin : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
    have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
    exact_mod_cast hpos
  have hw : 0 ≤ paperDifferentWeight K P := by
    unfold paperDifferentWeight
    exact div_nonneg (Nat.cast_nonneg _) hfin.le
  have hc : 0 ≤ ((normalizedFactors (differentIdeal ℤ (𝓞 K))).count P : ℝ) :=
    Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log ((pOf P).natAbs : ℝ) := by
    have h1 : (1 : ℝ) ≤ ((pOf P).natAbs : ℝ) := by
      have : 1 ≤ (pOf P).natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hpne)
      exact_mod_cast this
    exact Real.log_nonneg h1
  exact mul_nonneg (mul_nonneg hw hc) hlog

#print axioms paperWeightedDeltaSum_subset_le_logDifferentK


/-! ## 消掉 pOf/hover 参数（ℤ PID: 每个 P 的 under-ℤ 生成元） -/

/-- P.under ℤ 的生成元（ℤ 是 PID）。 -/
noncomputable def underIntGen (P : Ideal (𝓞 K)) : ℤ :=
  Submodule.IsPrincipal.generator (P.under ℤ)

/-- underIntGen 是 P.under ℤ 的生成元 ⇒ P LiesOver span {underIntGen}。 -/
theorem underIntGen_liesOver (P : Ideal (𝓞 K)) :
    P.LiesOver (Ideal.span {underIntGen K P}) := by
  have h := Submodule.IsPrincipal.span_singleton_generator (P.under ℤ)
  exact ⟨h⟩

/-- **无参数版**: logDifferentK = Σ_P w_P·δ_P·log(underIntGen P).natAbs。 -/
theorem paperWeightedDeltaSum_eq_logDifferentK' :
    (∑ P ∈ LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual.differentPlaces K,
        paperDifferentWeight K P *
          ((normalizedFactors (differentIdeal ℤ (𝓞 K))).count P : ℝ) *
            Real.log ((underIntGen K P).natAbs : ℝ)) =
      Real.log (NumberField.rootDiscr K) :=
  paperWeightedDeltaSum_eq_logDifferentK K (fun P => underIntGen (K := K) P) (fun P _ => underIntGen_liesOver (K := K) P)

/-- **无参数子集版**: S ⊆ differentPlaces ⇒ Σ_{P∈S} ≤ logDifferentK。 -/
theorem paperWeightedDeltaSum_subset_le_logDifferentK'
    (S : Finset (Ideal (𝓞 K)))
    (hS : S ⊆ LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual.differentPlaces K) :
    (∑ P ∈ S,
        paperDifferentWeight K P *
          ((normalizedFactors (differentIdeal ℤ (𝓞 K))).count P : ℝ) *
            Real.log ((underIntGen K P).natAbs : ℝ)) ≤
      Real.log (NumberField.rootDiscr K) :=
  paperWeightedDeltaSum_subset_le_logDifferentK K (fun P => underIntGen (K := K) P) (fun P _ => underIntGen_liesOver (K := K) P) S hS

#print axioms underIntGen_liesOver
#print axioms paperWeightedDeltaSum_eq_logDifferentK'
#print axioms paperWeightedDeltaSum_subset_le_logDifferentK'


/-! ## differentPlaces 成员/计数引理（供 badPlaceSet ⊆ differentPlaces 使用） -/

/-- P ∈ differentPlaces K ↔ δ_P = count P > 0。 -/
theorem mem_differentPlaces_iff (P : Ideal (𝓞 K)) :
    P ∈ LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual.differentPlaces K ↔
      0 < (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P := by
  rw [LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual.differentPlaces,
    Multiset.mem_toFinset, Multiset.count_pos]

/-- count 正 ⇒ P ∈ differentPlaces。 -/
theorem mem_differentPlaces_of_count_pos {P : Ideal (𝓞 K)}
    (h : 0 < (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P) :
    P ∈ LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual.differentPlaces K :=
  (mem_differentPlaces_iff K P).mpr h

/-- P ∈ differentPlaces ⇒ count 正。 -/
theorem count_pos_of_mem_differentPlaces {P : Ideal (𝓞 K)}
    (h : P ∈ LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual.differentPlaces K) :
    0 < (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P :=
  (mem_differentPlaces_iff K P).mp h

/-- P ∈ differentPlaces ⇒ P 是素理想。 -/
theorem prime_of_mem_differentPlaces {P : Ideal (𝓞 K)}
    (h : P ∈ LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual.differentPlaces K) :
    P.IsPrime := by
  have hI : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  exact ((Ideal.mem_normalizedFactors_iff hI).mp (Multiset.mem_toFinset.mp h)).1

/-- P ∈ differentPlaces ⇒ count P 非零（ℕ 形式）。 -/
theorem count_ne_zero_of_mem_differentPlaces {P : Ideal (𝓞 K)}
    (h : P ∈ LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual.differentPlaces K) :
    (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P ≠ 0 :=
  (count_pos_of_mem_differentPlaces K h).ne'

#print axioms mem_differentPlaces_iff
#print axioms prime_of_mem_differentPlaces

#print axioms paperDifferentWeight
#print axioms paperWeightedDeltaSum_eq_logDifferentK

end LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual