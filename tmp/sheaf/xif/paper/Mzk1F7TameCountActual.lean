import LeanFormal.IUT.IUTIV.Estimates.DifferentTameEquality
import tmp.sheaf.xif.paper.Mzk1F7DiscTameBoundActual
import tmp.sheaf.xif.paper.Mzk1F7DiscLocalGlobalActual
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Tactic
/-!
# F7 tame count from tame ramification conditions (route §8.5)

Mathlib/donor fact: for a general Dedekind extension `B/A`, a nonzero maximal `p`,
and a nonzero prime `P` over `p`, tame ramification at `P` (the ramification index
`e` is invertible in `A ⧸ p`, and `B ⧸ P` is separable over `A ⧸ p`) gives the
exact different exponent
`ord_P 𝔇_{B/A} = e - 1`
(donor `LeanFormal.IUT.IUTIV.Estimates.count_differentIdeal_eq_of_tame`).

Instantiating with `A = ℤ`, `B = 𝓞 K`, this file produces the `TameCount K p`
hypothesis consumed by `Mzk1F7DiscTameBoundActual.disc_factorization_le_finrank_of_tame`.
Hence `v_p(|disc K|) ≤ [K : ℚ]` follows from the two tame conditions alone.

Lead lane: H-T / P8-P.
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1F7TameCountActual

open Module Ideal UniqueFactorizationMonoid NumberField IsDedekindDomain
open LeanFormal.IUT.XiFPaper.Mzk1F7DiscTameBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1F7DiscLocalGlobalActual

variable {K : Type*} [Field K] [NumberField K]
variable {p : ℕ} [Fact p.Prime]

/-- The two tame-ramification conditions at `p`, stated for every prime `P` over `p`. -/
def TameRamifiedAt (K : Type*) [Field K] [NumberField K] (p : ℕ) : Prop :=
  ∀ (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})],
    Ideal.absNorm (Ideal.under ℤ P) = p →
      Algebra.IsSeparable (ℤ ⧸ Ideal.span {(p : ℤ)}) (𝓞 K ⧸ P) ∧
        ((Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) P : ℕ) :
          ℤ ⧸ Ideal.span {(p : ℤ)}) ≠ 0

/-- Route §8.5: tame ramification conditions give the exact local different exponent. -/
theorem tameCount_of_tameRamifiedAt (htame : TameRamifiedAt K p) : TameCount K p := by
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
  obtain ⟨hsep, he⟩ := htame P hcond
  haveI : Algebra.IsSeparable (ℤ ⧸ Ideal.span {(p : ℤ)}) (𝓞 K ⧸ P) := hsep
  exact LeanFormal.IUT.IUTIV.Estimates.count_differentIdeal_eq_of_tame
    (A := ℤ) (B := 𝓞 K) (p := Ideal.span {(p : ℤ)}) (P := P) hp0 hPne he

/-- Route §8.5 assembled: tame ramification at `p` gives `v_p(|disc K|) ≤ [K : ℚ]`. -/
theorem disc_factorization_le_finrank_of_tameRamifiedAt (htame : TameRamifiedAt K p) :
    (NumberField.discr K).natAbs.factorization p ≤ Module.finrank ℚ K :=
  disc_factorization_le_finrank_of_tame (tameCount_of_tameRamifiedAt htame)

end LeanFormal.IUT.XiFPaper.Mzk1F7TameCountActual
