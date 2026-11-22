import tmp.sheaf.xif.paper.S2660R10ModelActual
import tmp.sheaf.xif.paper.S2584PrimeDegreeOneActual

noncomputable section
set_option maxHeartbeats 8000000

open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual
open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2660R10ModelActual

namespace LeanFormal.IUT.XiFPaper.S2661P10Actual

abbrev A10 : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.C
abbrev R10 : Type := LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.R

noncomputable def p10 (W : S2584PrimeDegreeOneWitness) : Ideal R10 :=
  W.p.map (algebraMap A10 R10)

theorem h613_mem (W : S2584PrimeDegreeOneWitness) :
    algebraMap ℤ A10 (613 : ℤ) ∈ W.p := by
  have hL : W.p.under ℤ = Ideal.span ({(613 : ℤ)} : Set ℤ) :=
    W.p_liesOver.over.symm
  have h : (613 : ℤ) ∈ W.p.under ℤ := by
    rw [hL]
    exact Ideal.mem_span_singleton_self 613
  rwa [Ideal.mem_under] at h

theorem h10_not_mem (W : S2584PrimeDegreeOneWitness) :
    (algebraMap ℤ A10 (10 : ℤ)) ∉ W.p := by
  intro h10
  have h613 := h613_mem W
  have hcop : IsCoprime (algebraMap ℤ A10 (613 : ℤ))
      (algebraMap ℤ A10 (10 : ℤ)) :=
    (show IsCoprime (613 : ℤ) 10 by norm_num).map (algebraMap ℤ A10)
  obtain ⟨a, b, hab⟩ := hcop
  have hap : a * algebraMap ℤ A10 (613 : ℤ) ∈ W.p :=
    Ideal.mul_mem_left W.p a h613
  have hbp : b * algebraMap ℤ A10 (10 : ℤ) ∈ W.p :=
    Ideal.mul_mem_left W.p b h10
  have h1p : (1 : A10) ∈ W.p := by
    rw [← hab]
    exact Ideal.add_mem W.p hap hbp
  exact W.p_prime.ne_top (Ideal.eq_top_iff_one W.p |>.mpr h1p)

#check p10
theorem hdisj (W : S2584PrimeDegreeOneWitness) :
    Disjoint (Submonoid.powers (10 : A10) : Set A10) (W.p : Set A10) := by
  rw [Set.disjoint_left]
  intro x hx hxp
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff x (10 : A10)).mp hx
  subst hn
  cases n with
  | zero =>
      exact W.p_prime.ne_top (Ideal.eq_top_iff_one W.p |>.mpr (by simpa using hxp))
  | succ n =>
      exact h10_not_mem W (W.p_prime.mem_of_pow_mem (n + 1) hxp)

theorem p10_prime (W : S2584PrimeDegreeOneWitness) : (p10 W).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint (M := Submonoid.powers (10 : A10))
    R10 W.p W.p_prime (hdisj W)

theorem p10_ne_bot (W : S2584PrimeDegreeOneWitness) : p10 W ≠ ⊥ := by
  intro hbot
  have h613 : algebraMap A10 R10 (algebraMap ℤ A10 (613 : ℤ)) ∈ p10 W :=
    Ideal.mem_map_of_mem (algebraMap A10 R10) (h613_mem W)
  rw [hbot] at h613
  have hzero : algebraMap A10 R10 (algebraMap ℤ A10 (613 : ℤ)) = 0 := by
    simpa using h613
  have hM : Submonoid.powers (10 : A10) ≤ nonZeroDivisors A10 :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (by norm_num : (10 : A10) ≠ 0)
  have hinj : Function.Injective (algebraMap A10 R10) :=
    IsLocalization.injective R10 hM
  have h613ne : algebraMap A10 R10 (algebraMap ℤ A10 (613 : ℤ)) ≠ 0 := by
    intro hzero
    have h' : algebraMap ℤ A10 (613 : ℤ) = 0 :=
      hinj (by simpa using hzero)
    norm_num at h'
  exact h613ne hzero

theorem p10_isMaximal (W : S2584PrimeDegreeOneWitness) : (p10 W).IsMaximal := by
  have hM : Submonoid.powers (10 : A10) ≤ nonZeroDivisors A10 :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (by norm_num : (10 : A10) ≠ 0)
  haveI : IsDomain R10 :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers (10 : A10))
      (S := R10) hM
  haveI : IsDedekindDomain R10 :=
    IsLocalization.isDedekindDomain A10 hM R10
  exact Ideal.IsPrime.isMaximal (p10_prime W) (p10_ne_bot W)

#check p10_isMaximal

#check p10#check h10_not_mem

end LeanFormal.IUT.XiFPaper.S2661P10Actual
end
