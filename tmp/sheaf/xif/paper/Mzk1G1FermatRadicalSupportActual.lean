/- G1 section 8.5 (F7): tame different inputs and the radical discriminant bound

This file builds the arithmetic content of route section 8.5 (F7):

* radical support facts: radical n divides n, positivity, and the prime-support
  equivalence (p divides radical n iff p divides n) on a nonzero n;
* the logarithm of the radical as the sum of log p over n.primeFactors;
* the normalized log discriminant D(K) = log |disc K| / [K : Q] and the actual
  per-prime normalized contribution v_p(|disc K|) * log p / [K : Q], with the
  proved identity that their sum over (NumberField.discr K).natAbs.primeFactors is
  D(K) (log of the prime factorization);
* the section 8.5 tame-different summation: at p | abc with p not dividing n the
  normalized contribution is at most log p (the delta = e - 1 tame computation,
  applied place by place), while the finitely many p | n contribute a fixed C_n;
  summing over the support gives D(K) at most log rad(abc) + C_n.

The local tame input delta_w = e_w - 1 is supplied by
LeanFormal.IUT.IUTIV.Estimates.count_differentIdeal_eq_of_tame (with
logShellRamificationExponent_eq_ramificationIdx), and the p | n input by
LeanFormal.IUT.Foundations.LocalFields.localDifferentPaperOrder_le_degree_padicVal.
The transport v_p(disc K) = sum over w | p of f_w delta_w is exactly the hsupp/htame
input below; it is NOT claimed proved here.  Every statement below is proved
without placeholders or surrogate carriers.

Application inputs (to be supplied by the root-extension arithmetic, not proved
here): (i) p not dividing abc implies v_p(disc K) = 0 (the root extension is
etale/unramified at such p; Mathlib conversion is
NumberField.not_dvd_discr_iff_forall_liesOver/isUnramifiedIn, and the actual
unramifiedness comes from a unit derivative of the Kummer root polynomial);
(iii) the finitely many p | n contribute a constant C_n (local bound donor
Mzk1LpDifferentBoundActual.localDifferentPaperOrder_le_boundedDegree, localised to
the p-adic places of K); (hdiv) e_P divides n, from Kummer ramification of the root
extension.  The local-global dictionary for v_p(|disc K|) is
Mzk1F7DiscSumActual.disc_factorization_eq_multiset_sum.

-/
import tmp.sheaf.xif.paper.Mzk1G1EllipticHeightCriterionActual
import tmp.sheaf.xif.paper.Mzk1F7TameCountGlobalActual
import LeanFormal.IUT.IUTIV.Estimates.DifferentTameEquality
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentUpperBound
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.Tactic

noncomputable section
open scoped NumberField
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatRadicalSupportActual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual

/-! ## 1. The radical of abc: divisibility and prime support -/

theorem radical_eq_prod_primeFactors_f7 (n : Nat) :
    radical n = ∏ p ∈ n.primeFactors, p := by
  simp [radical]

theorem radical_dvd_self_f7 (n : Nat) : radical n ∣ n := by
  simpa [radical] using Nat.prod_primeFactors_dvd n

theorem radical_pos_f7 (n : Nat) : 0 < radical n := by
  unfold radical
  refine Finset.prod_pos ?_
  intro p hp
  exact Nat.pos_of_mem_primeFactors (by simpa using hp)

theorem prime_dvd_radical_iff_f7 {n p : Nat} (hp : p.Prime) (hn : n ≠ 0) :
    p ∣ radical n ↔ p ∣ n := by
  constructor
  · intro h
    rw [radical_eq_prod_primeFactors_f7] at h
    have hprime : _root_.Prime p := Nat.irreducible_iff_prime.mp hp
    obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hprime (fun q : Nat => q)).mp h
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqe : q = p := (hqprime.dvd_iff_eq hp.ne_one).mp hpq
    subst hqe
    exact Nat.dvd_of_mem_primeFactors hq
  · intro h
    rw [radical_eq_prod_primeFactors_f7]
    exact Finset.dvd_prod_of_mem (fun q : Nat => q) (Nat.Prime.mem_primeFactors hp h hn)

theorem prime_dvd_freyConductor_iff_f7 {a b c p : Nat} (hp : p.Prime)
    (habc : 0 < a * b * c) :
    p ∣ freyConductor a b c ↔ p ∣ a * b * c := by
  rw [freyConductor_eq_radical]
  exact prime_dvd_radical_iff_f7 hp habc.ne'

/-! ## 2. Logarithms of radicals and the tame contribution sum -/

theorem log_eq_sum_factorization_log {n : Nat} (hn : n ≠ 0) :
    Real.log (n : ℝ) = ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log (p : ℝ) := by
  have hnat := Nat.prod_primeFactors_pow_factorization (n := n) hn
  have hcast : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
    calc (n : ℝ) = ↑(∏ p ∈ n.primeFactors, p ^ n.factorization p) := by
          exact congrArg (fun m : Nat => (m : ℝ)) hnat
      _ = ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
          rw [Nat.cast_prod]
          exact Finset.prod_congr rfl (fun p _ => by rw [Nat.cast_pow])
  rw [hcast]
  rw [Real.log_prod]
  · refine Finset.sum_congr rfl ?_
    intro p _
    rw [Real.log_pow]
  · intro p hp
    exact pow_ne_zero _ (by exact_mod_cast (Nat.pos_of_mem_primeFactors hp).ne')

theorem log_radical_eq_sum_log {n : Nat} (hn : n ≠ 0) :
    Real.log (radical n : ℝ) = ∑ p ∈ n.primeFactors, Real.log (p : ℝ) := by
  rw [radical_eq_prod_primeFactors_f7]
  rw [Nat.cast_prod]
  rw [Real.log_prod]
  intro p hp
  exact Nat.cast_ne_zero.mpr (Nat.pos_of_mem_primeFactors hp).ne'

theorem log_radical_le_log {n : Nat} (hn : 0 < n) :
    Real.log (radical n : ℝ) ≤ Real.log (n : ℝ) := by
  refine Real.log_le_log ?_ ?_
  · exact_mod_cast radical_pos_f7 n
  · exact_mod_cast Nat.le_of_dvd hn (radical_dvd_self_f7 n)

theorem tame_log_sum_le_log_radical (a b c n : Nat) (habc : 0 < a * b * c) :
    (∑ p ∈ (a * b * c).primeFactors.filter (fun p => ¬ p ∣ n), Real.log (p : ℝ))
      ≤ Real.log (radical (a * b * c) : ℝ) := by
  rw [log_radical_eq_sum_log habc.ne']
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro p hp _
  exact Real.log_nonneg (by exact_mod_cast (Nat.pos_of_mem_primeFactors hp))

theorem f7_sum_bound (a b c n : Nat) (habc : 0 < a * b * c) (hn : 0 < n)
    (contrib : Nat → ℝ) (C : ℝ)
    (htame : ∀ p ∈ (a * b * c).primeFactors, ¬ p ∣ n → contrib p ≤ Real.log (p : ℝ))
    (hbad : (∑ p ∈ n.primeFactors, contrib p) ≤ C) :
    (∑ p ∈ (a * b * c).primeFactors ∪ n.primeFactors, contrib p)
      ≤ Real.log (radical (a * b * c) : ℝ) + C := by
  have hdisj : Disjoint ((a * b * c).primeFactors.filter (fun p => ¬ p ∣ n)) n.primeFactors := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    exact (Finset.mem_filter.mp hp).2 (Nat.dvd_of_mem_primeFactors hp')
  have hunion : (a * b * c).primeFactors ∪ n.primeFactors =
      ((a * b * c).primeFactors.filter (fun p => ¬ p ∣ n)) ∪ n.primeFactors := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_union.mp hp with h | h
      · by_cases hpn : p ∣ n
        · refine Finset.mem_union.mpr (Or.inr ?_)
          exact Nat.Prime.mem_primeFactors (Nat.prime_of_mem_primeFactors h) hpn hn.ne'
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨h, hpn⟩))
      · exact Finset.mem_union.mpr (Or.inr h)
    · intro hp
      rcases Finset.mem_union.mp hp with h | h
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mp h).1)
      · exact Finset.mem_union.mpr (Or.inr h)
  rw [hunion, Finset.sum_union hdisj]
  have htamesum :
      (∑ p ∈ (a * b * c).primeFactors.filter (fun p => ¬ p ∣ n), contrib p)
        ≤ ∑ p ∈ (a * b * c).primeFactors.filter (fun p => ¬ p ∣ n), Real.log (p : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro p hp
    exact htame p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
  have hlog := tame_log_sum_le_log_radical a b c n habc
  linarith

/-! ## 3. The actual normalized log discriminant of a number field -/

def normalizedLogDisc (K : Type*) [Field K] [NumberField K] : ℝ :=
  Real.log ((NumberField.discr K).natAbs : ℝ) / (Module.finrank ℚ K : ℝ)

def differentContribution (K : Type*) [Field K] [NumberField K] (p : Nat) : ℝ :=
  (((NumberField.discr K).natAbs.factorization p : ℝ) * Real.log (p : ℝ))
    / (Module.finrank ℚ K : ℝ)

theorem log_natAbs_discr_eq_sum_factorization (K : Type*) [Field K] [NumberField K] :
    Real.log ((NumberField.discr K).natAbs : ℝ) =
      ∑ p ∈ (NumberField.discr K).natAbs.primeFactors,
        ((NumberField.discr K).natAbs.factorization p : ℝ) * Real.log (p : ℝ) := by
  have hne : (NumberField.discr K).natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K)
  exact log_eq_sum_factorization_log hne

theorem sum_differentContribution_eq_normalizedLogDisc (K : Type*) [Field K] [NumberField K]
    (hdeg : 0 < Module.finrank ℚ K) :
    (∑ p ∈ (NumberField.discr K).natAbs.primeFactors, differentContribution K p)
      = normalizedLogDisc K := by
  unfold differentContribution normalizedLogDisc
  rw [← Finset.sum_div]
  congr 1
  exact (log_natAbs_discr_eq_sum_factorization K).symm

theorem differentContribution_nonneg (K : Type*) [Field K] [NumberField K]
    (hdeg : 0 < Module.finrank ℚ K) {p : Nat} (hp : p.Prime) :
    0 ≤ differentContribution K p := by
  unfold differentContribution
  have hdeg' : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast hdeg
  have hlog : 0 ≤ Real.log (p : ℝ) := by
    refine Real.log_nonneg ?_
    exact_mod_cast (Nat.Prime.one_lt hp).le
  have hfac : (0 : ℝ) ≤ ((NumberField.discr K).natAbs.factorization p : ℝ) := by
    exact_mod_cast Nat.zero_le _
  exact div_nonneg (mul_nonneg hfac hlog) hdeg'.le

theorem f7_normalizedLogDisc_le (K : Type*) [Field K] [NumberField K]
    (a b c n : Nat) (habc : 0 < a * b * c) (hn : 0 < n) (hdeg : 0 < Module.finrank ℚ K) (C : ℝ)
    (hsupp : (NumberField.discr K).natAbs.primeFactors ⊆
      (a * b * c).primeFactors ∪ n.primeFactors)
    (htame : ∀ p ∈ (a * b * c).primeFactors, ¬ p ∣ n →
      differentContribution K p ≤ Real.log (p : ℝ))
    (hbad : (∑ p ∈ n.primeFactors, differentContribution K p) ≤ C) :
    normalizedLogDisc K ≤ Real.log (radical (a * b * c) : ℝ) + C := by
  rw [← sum_differentContribution_eq_normalizedLogDisc K hdeg]
  have hsubset :
      (∑ p ∈ (NumberField.discr K).natAbs.primeFactors, differentContribution K p)
        ≤ ∑ p ∈ (a * b * c).primeFactors ∪ n.primeFactors, differentContribution K p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsupp ?_
    intro p hp _
    rcases Finset.mem_union.mp hp with h | h
    · exact differentContribution_nonneg K hdeg (Nat.prime_of_mem_primeFactors h)
    · exact differentContribution_nonneg K hdeg (Nat.prime_of_mem_primeFactors h)
  have hbound := f7_sum_bound a b c n habc hn (differentContribution K) C htame hbad
  linarith

/-! ## 4. Wiring the tame/disc factorization input into the F7 bound -/

/-- Per-prime tame bound: v_p(|disc K|) <= [K:Q] makes the normalized different
contribution at p at most log p. -/
theorem differentContribution_le_log_of_factorization_le (K : Type*) [Field K] [NumberField K]
    (hdeg : 0 < Module.finrank ℚ K) {p : Nat} (hp : p.Prime)
    (h : (NumberField.discr K).natAbs.factorization p ≤ Module.finrank ℚ K) :
    differentContribution K p ≤ Real.log (p : ℝ) := by
  unfold differentContribution
  have hdeg' : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast hdeg
  have hlog : 0 ≤ Real.log (p : ℝ) := by
    refine Real.log_nonneg ?_
    exact_mod_cast (Nat.Prime.one_lt hp).le
  have hfac : ((NumberField.discr K).natAbs.factorization p : ℝ) ≤
      (Module.finrank ℚ K : ℝ) := by exact_mod_cast h
  rw [div_le_iff₀ hdeg']
  have hmul : ((NumberField.discr K).natAbs.factorization p : ℝ) * Real.log (p : ℝ) ≤
      (Module.finrank ℚ K : ℝ) * Real.log (p : ℝ) :=
    mul_le_mul_of_nonneg_right hfac hlog
  linarith

/-- F7 with the tame/disc-factorization input: unramified outside rad(abc) and
v_p(|disc K|) <= [K:Q] at the tame primes p | abc, p not dividing n, plus the fixed
p | n contribution, give D(K) <= log rad(abc) + C. -/
theorem f7_normalizedLogDisc_le_of_tame (K : Type*) [Field K] [NumberField K]
    (a b c n : Nat) (habc : 0 < a * b * c) (hn : 0 < n) (hdeg : 0 < Module.finrank ℚ K)
    (C : ℝ)
    (hzero : ∀ p, p.Prime → ¬ p ∣ a * b * c →
      (NumberField.discr K).natAbs.factorization p = 0)
    (htame : ∀ p ∈ (a * b * c).primeFactors, ¬ p ∣ n →
      (NumberField.discr K).natAbs.factorization p ≤ Module.finrank ℚ K)
    (hbad : (∑ p ∈ n.primeFactors, differentContribution K p) ≤ C) :
    normalizedLogDisc K ≤ Real.log (radical (a * b * c) : ℝ) + C := by
  refine f7_normalizedLogDisc_le K a b c n habc hn hdeg C ?_ ?_ hbad
  · intro p hp
    have hpdata := Nat.mem_primeFactors.mp hp
    have hpprime : p.Prime := hpdata.1
    have hpdvd : p ∣ (NumberField.discr K).natAbs := hpdata.2.1
    have hpne : (NumberField.discr K).natAbs ≠ 0 := hpdata.2.2
    by_cases habc_dvd : p ∣ a * b * c
    · exact Finset.mem_union.mpr (Or.inl
        (Nat.Prime.mem_primeFactors hpprime habc_dvd (Nat.pos_iff_ne_zero.mp habc)))
    · exfalso
      have hpos := hpprime.factorization_pos_of_dvd hpne hpdvd
      have hz := hzero p hpprime habc_dvd
      omega
  · intro p hp hpn
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    exact differentContribution_le_log_of_factorization_le K hdeg hpprime (htame p hp hpn)

#print axioms differentContribution_le_log_of_factorization_le
#print axioms f7_normalizedLogDisc_le_of_tame


/-- F7 with the root-extension ramification-divisibility input (hdiv: e_P divides n;
in applications this comes from Kummer ramification of the Fermat root extension): the per-prime tame
factorization bound is discharged by the global tame count
(Mzk1F7TameCountGlobalActual.disc_factorization_le_finrank_of_div_ramification). -/
theorem f7_normalizedLogDisc_le_of_div_ramification (K : Type*) [Field K] [NumberField K]
    (a b c n : Nat) (habc : 0 < a * b * c) (hn : 0 < n) (hdeg : 0 < Module.finrank ℚ K)
    (C : ℝ)
    (hzero : ∀ p, p.Prime → ¬ p ∣ a * b * c →
      (NumberField.discr K).natAbs.factorization p = 0)
    (hdiv : ∀ p ∈ (a * b * c).primeFactors, ¬ p ∣ n →
      ∀ P ∈ (UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ (𝓞 K))).toFinset,
        Ideal.absNorm (Ideal.under ℤ P) = p →
        Ideal.ramificationIdx' (Ideal.span {(p : Int)}) P ∣ n)
    (hbad : (∑ p ∈ n.primeFactors, differentContribution K p) ≤ C) :
    normalizedLogDisc K ≤ Real.log (radical (a * b * c) : ℝ) + C := by
  refine f7_normalizedLogDisc_le_of_tame K a b c n habc hn hdeg C hzero ?_ hbad
  intro p hp hpn
  haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  exact LeanFormal.IUT.XiFPaper.Mzk1F7TameCountGlobalActual.disc_factorization_le_finrank_of_div_ramification
    (K := K) (p := p) (n := n) (hdiv p hp hpn) hpn

#print axioms f7_normalizedLogDisc_le_of_div_ramification

end LeanFormal.IUT.XiFPaper.Mzk1G1FermatRadicalSupportActual
end