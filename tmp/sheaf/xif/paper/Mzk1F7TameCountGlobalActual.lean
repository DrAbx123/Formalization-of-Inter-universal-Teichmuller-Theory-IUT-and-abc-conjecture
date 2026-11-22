import tmp.sheaf.xif.paper.Mzk1F7DiscTameBoundActual
import tmp.sheaf.xif.paper.Mzk1G1FermatRadicalSupportFinal3Actual
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Tactic
/-!
# F7 htame: global tame count from the two arithmetic inputs

Using the residue separability residue_separable_global (finite residue fields are
perfect) and the tameness arithmetic ramificationIdx_invertible_of_dvd (e divides n
and p does not divide n imply e is invertible mod p), the tame different exponent
count_P(D) = e - 1 holds globally, hence v_p(|disc K|) <= [K : Q].

Remaining arithmetic input: e_P divides n for every normalized factor over p.

Lead lane: H-T / P8-P (F7 htame).
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1F7TameCountGlobalActual

open Module Ideal UniqueFactorizationMonoid NumberField IsDedekindDomain
open LeanFormal.IUT.XiFPaper.Mzk1F7DiscTameBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatRadicalSupportFinal3Actual

variable {K : Type*} [Field K] [NumberField K]
variable {p n : ℕ} [Fact p.Prime]

/-- Route 8.5 htame, from the ramification-divisibility arithmetic input. -/
theorem tameCount_of_div_ramification
    (hdiv : ∀ P ∈ (normalizedFactors (differentIdeal ℤ (𝓞 K))).toFinset,
      Ideal.absNorm (Ideal.under ℤ P) = p → Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) P ∣ n)
    (hpn : ¬ p ∣ n) : TameCount K p := by
  intro P hP hcond
  haveI hpm : (Ideal.span {(p : ℤ)}).IsMaximal := span_prime_isMaximal p
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hmem : P ∈ normalizedFactors (differentIdeal ℤ (𝓞 K)) := Multiset.mem_toFinset.mp hP
  have hprime : Prime P := prime_of_normalized_factor P hmem
  have hPne : P ≠ ⊥ := hprime.ne_zero
  have hPisPrime : P.IsPrime := (Ideal.prime_iff_isPrime hPne).mp hprime
  haveI : P.IsPrime := hPisPrime
  haveI : P.IsMaximal := hPisPrime.isMaximal hPne
  have hunder : Ideal.under ℤ P = Ideal.span {(p : ℤ)} := by
    rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ P), hcond]
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := hunder ▸ inferInstance
  haveI : Algebra.IsSeparable (ℤ ⧸ Ideal.span {(p : ℤ)}) (𝓞 K ⧸ P) :=
    residue_separable_global P
  have he : ((Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) P : ℕ) :
      ℤ ⧸ Ideal.span {(p : ℤ)}) ≠ 0 := by
    simpa using ramificationIdx_invertible_of_dvd
      (p := p) (e := Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) P) (n := n)
      (hdiv P hP hcond) hpn
  exact LeanFormal.IUT.IUTIV.Estimates.count_differentIdeal_eq_of_tame
    (A := ℤ) (B := 𝓞 K) (p := Ideal.span {(p : ℤ)}) (P := P) hp0 hPne he

/-- Route 8.5 assembled: v_p(|disc K|) <= [K : Q] from the tameness arithmetic input. -/
theorem disc_factorization_le_finrank_of_div_ramification
    (hdiv : ∀ P ∈ (normalizedFactors (differentIdeal ℤ (𝓞 K))).toFinset,
      Ideal.absNorm (Ideal.under ℤ P) = p → Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) P ∣ n)
    (hpn : ¬ p ∣ n) :
    (NumberField.discr K).natAbs.factorization p ≤ Module.finrank ℚ K :=
  disc_factorization_le_finrank_of_tame (tameCount_of_div_ramification hdiv hpn)

end LeanFormal.IUT.XiFPaper.Mzk1F7TameCountGlobalActual
