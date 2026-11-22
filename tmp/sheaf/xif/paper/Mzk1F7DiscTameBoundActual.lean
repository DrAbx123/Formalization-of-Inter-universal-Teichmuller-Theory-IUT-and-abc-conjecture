import tmp.sheaf.xif.paper.Mzk1F7DiscSumActual
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Tactic
/-!
# F7 tame discriminant bound (route §8.5), main assembly

Tame local count input plus the fundamental identity give
`v_p(|disc K|) ≤ [K : ℚ]`, i.e. `differentContribution K p ≤ log p`.

Lead lane: H-T / P8-P.
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1F7DiscTameBoundActual

open Module Ideal UniqueFactorizationMonoid NumberField IsDedekindDomain
open LeanFormal.IUT.XiFPaper.Mzk1F7DiscSumActual

variable {K : Type*} [Field K] [NumberField K]
variable {p : ℕ} [Fact p.Prime]

/-- Tame local count input: every normalized factor of the global different ideal
lying over `p` has multiplicity `e - 1`. -/
def TameCount (K : Type*) [Field K] [NumberField K] (p : ℕ) : Prop :=
  ∀ P ∈ (normalizedFactors (differentIdeal ℤ (𝓞 K))).toFinset,
    Ideal.absNorm (Ideal.under ℤ P) = p →
      (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P =
        Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) P - 1

/-- The rational prime ideal `(p)` is maximal in ℤ. -/
theorem span_prime_isMaximal (p : ℕ) [Fact p.Prime] :
    (Ideal.span {(p : ℤ)}).IsMaximal := by
  have hpint : Prime (p : ℤ) :=
    Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : p.Prime))
  have hne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hprime : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hne).mpr hpint
  exact hprime.isMaximal (Ideal.span_singleton_eq_bot.not.mpr hne)

/-- Route §8.5 tame bound: `v_p(|disc K|) ≤ [K : ℚ]`. -/
theorem disc_factorization_le_finrank_of_tame (hcount : TameCount K p) :
    (NumberField.discr K).natAbs.factorization p ≤ Module.finrank ℚ K := by
  classical
  haveI hpm : (Ideal.span {(p : ℤ)}).IsMaximal := span_prime_isMaximal p
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hfin := Ideal.sum_ramification_inertia (R := ℤ) (S := 𝓞 K) (K := ℚ) (L := K)
    (p := Ideal.span {(p : ℤ)}) hp0
  rw [disc_factorization_eq_multiset_sum]
  rw [Finset.sum_multiset_map_count]
  set T := normalizedFactors (differentIdeal ℤ (𝓞 K)) with hT
  have hstep : (∑ m ∈ T.toFinset,
        Multiset.count m T •
          (if Ideal.absNorm (Ideal.under ℤ m) = p then m.inertiaDeg ℤ else 0))
      = ∑ m ∈ T.toFinset.filter (fun m => Ideal.absNorm (Ideal.under ℤ m) = p),
          Multiset.count m T * m.inertiaDeg ℤ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro m _
    by_cases h : Ideal.absNorm (Ideal.under ℤ m) = p <;> simp [h]
  rw [hstep]
  have hmid : (∑ m ∈ T.toFinset.filter (fun m => Ideal.absNorm (Ideal.under ℤ m) = p),
        Multiset.count m T * m.inertiaDeg ℤ)
      ≤ ∑ m ∈ T.toFinset.filter (fun m => Ideal.absNorm (Ideal.under ℤ m) = p),
          Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) m *
            Ideal.inertiaDeg' (Ideal.span {(p : ℤ)}) m := by
    refine Finset.sum_le_sum ?_
    intro m hm
    obtain ⟨hms, hcondm⟩ := Finset.mem_filter.mp hm
    have hmem : m ∈ T := Multiset.mem_toFinset.mp hms
    have hprime : Prime m := prime_of_normalized_factor m (hT ▸ hmem)
    have hne : m ≠ ⊥ := hprime.ne_zero
    have hprimeI : m.IsPrime := (Ideal.prime_iff_isPrime hne).mp hprime
    haveI : m.IsPrime := hprimeI
    haveI : m.IsMaximal := hprimeI.isMaximal hne
    have hunder : Ideal.under ℤ m = Ideal.span {(p : ℤ)} := by
      rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ m), hcondm]
    haveI : m.LiesOver (Ideal.span {(p : ℤ)}) := hunder ▸ inferInstance
    have hf : m.inertiaDeg ℤ = Ideal.inertiaDeg' (Ideal.span {(p : ℤ)}) m :=
      (Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(p : ℤ)}) m).symm
    rw [hf]
    have hc : Multiset.count m T = Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) m - 1 :=
      hcount m (hT ▸ hms) hcondm
    rw [hc]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  refine le_trans hmid ?_
  rw [← hfin]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro m hm
    obtain ⟨hms, hcondm⟩ := Finset.mem_filter.mp hm
    have hmem : m ∈ T := Multiset.mem_toFinset.mp hms
    have hprime : Prime m := prime_of_normalized_factor m (hT ▸ hmem)
    have hne : m ≠ ⊥ := hprime.ne_zero
    have hprimeP : m.IsPrime := (Ideal.prime_iff_isPrime hne).mp hprime
    have hunder : Ideal.under ℤ m = Ideal.span {(p : ℤ)} := by
      rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ m), hcondm]
    haveI : m.LiesOver (Ideal.span {(p : ℤ)}) := hunder ▸ inferInstance
    exact (IsDedekindDomain.mem_primesOverFinset_iff (p := Ideal.span {(p : ℤ)})
      (B := 𝓞 K) hp0).mpr ⟨hprimeP, inferInstance⟩
  · intro m _ _
    exact Nat.zero_le _

end LeanFormal.IUT.XiFPaper.Mzk1F7DiscTameBoundActual
