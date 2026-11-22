import LeanFormal.IUT.Foundations.PAdicAnalytic.TateInverseJFinal
import Mathlib.Algebra.Order.Ring.IsNonarchimedean

noncomputable section
open LeanFormal.IUT.PAdicAnalytic
open LeanFormal.IUT.PAdicAnalytic.General

namespace LeanFormal.IUT.XiFPaper.Node09TateFixedPointActual

local instance fivePrimeFactFP : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

universe u
variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  [CharZero K] [IsUltrametricDist K]

/-- Principal-term lemma: if H(q)=q+R(q)=t and the remainder is strictly smaller
than q in norm, then |q|=|t| in the p-adic norm. -/
theorem norm_eq_of_H_eq_t_of_remainder_lt
    {H R : ℚ_[5] → ℚ_[5]} {q t : ℚ_[5]}
    (hH : H q = q + R q) (hq : H q = t) (hlt : ‖R q‖ < ‖q‖) :
    ‖q‖ = ‖t‖ := by
  have hne : ‖q‖ ≠ ‖R q‖ := ne_of_gt hlt
  have hmax : ‖q + R q‖ = max ‖q‖ ‖R q‖ := Padic.add_eq_max_of_ne (p := 5) hne
  rw [hH] at hq
  rw [← hq, hmax, max_eq_left hlt.le]

/-- The actual Tate fixed point from the existing contraction theorem: for every
0<|t|<1 there is q with H(q)=t, j(q)=t^{-1} and |q|<1.  This is the §5.1
fixed-point construction; the remainder is the norm equality |q|=|t|. -/
theorem exists_actualTateQ
    (hint : ∀ n : ℕ, ‖(n : ℚ_[5])‖ ≤ 1)
    (h1728 : ‖(1728 : ℚ_[5])‖ = 1)
    {t : ℚ_[5]} (ht0 : t ≠ 0) (ht1 : ‖t‖ < 1) :
    ∃ q : ℚ_[5], tateHK q = t ∧ tateJK q = t⁻¹ ∧ ‖q‖ < 1 :=
  exists_tateHK_eq_and_tateJK_eq_inv (K := ℚ_[5]) hint h1728 ht0 ht1

/-- Exact status of the §5.1 route. -/
def Node09TateFixedPointStatus : List String :=
  [ "actual fixed point EXISTS in the tree: exists_tateHK_eq_and_tateJK_eq_inv (TateInverseJFinal) constructs q with tateHK q = t, tateJK q = t^{-1}, ||q|| < 1 for every 0<||t||<1, via exists_inverseJ_of_remainder / TateContractionGeneral closed-ball contraction. The iteration is the fixed point of q ↦ t - R(q) with H=q+R",
    "the contraction bounds are proved: generalTateRemainder_norm_le_c_sq (||R q|| <= c^2 on ||q||<=c) and generalTateRemainder_lipschitz_c (dist (R x) (R y) <= c*dist x y), with c=(1+||t||)/2 in TateInverseJFinal",
    "PROVED: exists_actualTateQ_norm_eq gives q with tateHK q = t, tateJK q = t^{-1}, ||q||<1 and ||q||=||t||. The strict remainder bound follows from the quadratic estimate generalTateRemainder_norm_le_of_le_c (c=||q||) and ||q||^2<||q||, then norm_eq_of_H_eq_t_of_remainder_lt",
    "no missing strict-remainder lemma remains for the fixed-point norm identity; the only hypotheses are hint/h1728 and 0<||t||<1",
    "no fake and no new axiom" ]

/-- Actual Tate q with the norm identity |q|=|t|.  The fixed point q is
produced by the existing contraction theorem; the strict remainder bound
follows from the quadratic remainder estimate (R starts at q^2) and |q|<1. -/
theorem exists_actualTateQ_norm_eq
    (hint : ∀ n : ℕ, ‖(n : ℚ_[5])‖ ≤ 1)
    (h1728 : ‖(1728 : ℚ_[5])‖ = 1)
    {t : ℚ_[5]} (ht0 : t ≠ 0) (ht1 : ‖t‖ < 1) :
    ∃ q : ℚ_[5], tateHK q = t ∧ tateJK q = t⁻¹ ∧
      ‖q‖ < 1 ∧ ‖q‖ = ‖t‖ := by
  obtain ⟨q, hqH, hqJ, hq1⟩ :=
    exists_tateHK_eq_and_tateJK_eq_inv (K := ℚ_[5]) hint h1728 ht0 ht1
  have hH0 : tateHK (0 : ℚ_[5]) = 0 := by
    have h := tateHK_eq_q_add_generalTateR (K := ℚ_[5]) hint h1728
      (by norm_num : ‖(0 : ℚ_[5])‖ < 1)
    simpa [generalTateR, generalTateRemainder] using h
  have hq0 : q ≠ 0 := by
    intro hq
    apply ht0
    rw [← hqH, hq, hH0]
  have hEq : tateHK q = q + generalTateR q :=
    tateHK_eq_q_add_generalTateR (K := ℚ_[5]) hint h1728 hq1
  have hnormR : ‖generalTateR q‖ ≤ ‖q‖ ^ 2 := by
    have h := generalTateRemainder_norm_le_of_le_c (K := ℚ_[5])
      (h := fun n : ℕ => (HK (K := ℚ_[5])).coeff n)
      (HK_coeff_norm_le_one (K := ℚ_[5]) hint h1728)
      (c := ‖q‖) hq1 (le_rfl)
    simpa [generalTateR, generalTateRemainder] using h
  have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have hsq_lt : ‖q‖ ^ 2 < ‖q‖ := by nlinarith [hqpos, hq1]
  have hlt : ‖generalTateR q‖ < ‖q‖ := lt_of_le_of_lt hnormR hsq_lt
  have hnorm := norm_eq_of_H_eq_t_of_remainder_lt
    (H := fun x : ℚ_[5] => tateHK x) (R := fun x : ℚ_[5] => generalTateR x)
    (q := q) (t := t) hEq hqH hlt
  exact ⟨q, hqH, hqJ, hq1, hnorm⟩

end LeanFormal.IUT.XiFPaper.Node09TateFixedPointActual
