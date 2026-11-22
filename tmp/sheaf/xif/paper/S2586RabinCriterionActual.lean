import tmp.sheaf.xif.paper.S2583FactorDegreeActual
import tmp.sheaf.xif.paper.S2550TwoFactorCertificateActual
import Mathlib
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual

namespace LeanFormal.IUT.XiFPaper.S2586RabinCriterionActual

local instance : Fact (Nat.Prime 1249) := ⟨by norm_num⟩

abbrev F10 : (ZMod 1249)[X] := S2550F10

theorem F10_monic : F10.Monic := by
  unfold F10 S2550F10
  apply Polynomial.monic_of_degree_le 10
  · compute_degree!
  · simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]

theorem F10_natDegree : F10.natDegree = 10 := by
  unfold F10 S2550F10
  compute_degree!

/-- Any reducible degree-10 polynomial over a field has a monic irreducible factor
of degree at most 5. -/
theorem exists_small_irreducible_factor (hred : ¬ Irreducible F10) :
    ∃ g : (ZMod 1249)[X], g.Monic ∧ Irreducible g ∧ g ∣ F10 ∧ g.natDegree ≤ 5 := by
  have hnotunit : ¬ IsUnit F10 :=
    Polynomial.not_isUnit_of_natDegree_pos F10 (by rw [F10_natDegree]; norm_num)
  obtain ⟨g, hgmonic, hgirr, hgdvd⟩ := Polynomial.exists_monic_irreducible_factor F10 hnotunit
  by_cases hgdeg : g.natDegree ≤ 5
  · exact ⟨g, hgmonic, hgirr, hgdvd, hgdeg⟩
  · -- g has degree at least 6; the complementary factor has degree at most 4
    have hg6 : 6 ≤ g.natDegree := by omega
    let q : (ZMod 1249)[X] := F10 /ₘ g
    have hmod : F10 %ₘ g = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd hgmonic).mpr hgdvd
    have hF10_ne0 : F10 ≠ 0 := by
      intro hF0
      have h := F10_natDegree
      rw [hF0] at h
      simp at h
    have hqmul : g * q = F10 := by
      have h := Polynomial.modByMonic_add_div F10 g
      rw [hmod, zero_add] at h
      exact h
    have hq_ne0 : q ≠ 0 := by
      intro hq0
      exact hF10_ne0 (by rw [← hqmul, hq0, mul_zero])
    have hqnotunit : ¬ IsUnit q := by
      intro hqunit
      have hqdeg0 : q.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hqunit
      have hqdeg : q.natDegree = 10 - g.natDegree := by
        simpa [q, F10_natDegree] using Polynomial.natDegree_divByMonic F10 hgmonic
      rw [hqdeg] at hqdeg0
      have hgle : g.natDegree ≤ 10 := by
        rw [← F10_natDegree]
        exact Polynomial.natDegree_le_of_dvd hgdvd hF10_ne0
      have hg10 : g.natDegree = 10 := by omega
      have hgF : F10 = g := Polynomial.eq_of_monic_of_dvd_of_natDegree_le
        hgmonic F10_monic hgdvd (by rw [F10_natDegree, hg10])
      exact hred (hgF.symm ▸ hgirr)
    obtain ⟨h, hhmonic, hhirr, hhdvdq⟩ := Polynomial.exists_monic_irreducible_factor q hqnotunit
    refine ⟨h, hhmonic, hhirr, ?_, ?_⟩
    · have hdiv : h ∣ g * q := by
        rw [mul_comm]
        exact dvd_mul_of_dvd_left hhdvdq g
      simpa [hqmul] using hdiv
    · calc h.natDegree ≤ q.natDegree := Polynomial.natDegree_le_of_dvd hhdvdq hq_ne0
        _ = 10 - g.natDegree := by
            simpa [q, F10_natDegree] using Polynomial.natDegree_divByMonic F10 hgmonic
        _ ≤ 5 := by omega

/-- Rabin irreducibility criterion for the degree-ten factor `F10`, conditional on
the Frobenius congruence at exponent 1249^10 and Bezout identities at d = 1..5. -/
theorem rabin_criterion
    (hcong : F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 ^ 10) - X)
    (hbez : ∀ d : ℕ, 1 ≤ d → d ≤ 5 →
      ∃ A B : (ZMod 1249)[X], A * F10 + B * ((X : (ZMod 1249)[X]) ^ (1249 ^ d) - X) = 1) :
    Irreducible F10 := by
  by_contra hred
  obtain ⟨g, hgmonic, hgirr, hgdvd, hgdeg⟩ := exists_small_irreducible_factor hred
  have hgpos : 1 ≤ g.natDegree := Nat.succ_le_of_lt (Irreducible.natDegree_pos hgirr)
  have hgdvdS : g ∣ (X : (ZMod 1249)[X]) ^ (1249 ^ g.natDegree) - X := by
    have h := LeanFormal.IUT.XiFPaper.S2583FactorDegreeActual.irreducible_dvd_X_pow_card_pow_sub_X
      (K := ZMod 1249) (g := g) hgirr hgmonic
    simpa using h
  obtain ⟨A, B, hAB⟩ := hbez g.natDegree hgpos hgdeg
  have hg_dvd_A : g ∣ A * F10 := dvd_mul_of_dvd_right hgdvd A
  have hg_dvd_B : g ∣ B * ((X : (ZMod 1249)[X]) ^ (1249 ^ g.natDegree) - X) :=
    dvd_mul_of_dvd_right hgdvdS B
  have hg_dvd_one : g ∣ (1 : (ZMod 1249)[X]) := by
    rw [← hAB]
    exact dvd_add hg_dvd_A hg_dvd_B
  exact hgirr.not_isUnit (isUnit_of_dvd_one hg_dvd_one)

#check rabin_criterion
#check exists_small_irreducible_factor

end LeanFormal.IUT.XiFPaper.S2586RabinCriterionActual
end
