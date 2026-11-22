/- T-avoidance for `phiFixedL`: at a protected point the value of `h(u)` equals the
constant `h(0)` modulo the prime, and the composite `Q -> R n -> R n / P` is injective
(a nonzero rational constant is a unit, so it cannot lie in a proper prime). -/
import tmp.sheaf.xif.paper.Mzk1G1PsiPhiDTAvoidActual
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiPhiTAvoidActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiPhiDTActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiPhiDTAvoidActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual

/-- A nonzero rational constant, viewed in the chart ring, is a unit. -/
theorem isUnit_algebraMap_rat {n : Nat} {c : ℚ} (hc : c ≠ 0) :
    IsUnit (algebraMap ℚ (R n) c) := by
  refine isUnit_iff_exists_inv.mpr ⟨algebraMap ℚ (R n) c⁻¹, ?_⟩
  rw [← map_mul, mul_inv_cancel₀ hc, map_one]

/-- The composite `Q -> R n -> R n / P` is injective for a prime `P`. -/
theorem quotient_rat_injective {n : Nat} (P : Ideal (R n)) [P.IsPrime] :
    Function.Injective ((Ideal.Quotient.mk P).comp (algebraMap ℚ (R n))) := by
  intro a b hab
  by_contra hne
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hmem : algebraMap ℚ (R n) (a - b) ∈ P := by
    have h' : Ideal.Quotient.mk P (algebraMap ℚ (R n) a) =
        Ideal.Quotient.mk P (algebraMap ℚ (R n) b) := hab
    have h'' := Ideal.Quotient.eq.mp h'
    rwa [← map_sub] at h''
  have htop : P = ⊤ := Ideal.eq_top_of_isUnit_mem P hmem (isUnit_algebraMap_rat hsub)
  exact (inferInstance : P.IsPrime).ne_top htop

/-- **T-avoidance at 0**. -/
theorem phiFixedL_T_avoid_zero {n : Nat} {T : Finset ℚ}
    (P : Ideal (R n)) [P.IsPrime] (hu : psiChart0Coord n T ∈ P) {h : Polynomial ℚ}
    (h0 : Polynomial.eval 0 h ≠ 0) :
    Ideal.Quotient.mk P (Polynomial.aeval (psiChart0Coord n T) h) ≠ 0 := by
  rw [phiFixedL_chart0_value_eq_at_DT P hu h]
  have hinj := quotient_rat_injective P
  intro hc
  have hzero : (Ideal.Quotient.mk P).comp (algebraMap ℚ (R n)) (Polynomial.eval 0 h) =
      (Ideal.Quotient.mk P).comp (algebraMap ℚ (R n)) 0 := by
    simpa using hc
  exact h0 (hinj hzero)

/-- **T-avoidance at 1**. -/
theorem phiFixedL_T_avoid_one {n : Nat} {T : Finset ℚ}
    (P : Ideal (R n)) [P.IsPrime] (hu : psiChart0Coord n T ∈ P) {h : Polynomial ℚ}
    (h1 : Polynomial.eval 0 h ≠ 1) :
    Ideal.Quotient.mk P (Polynomial.aeval (psiChart0Coord n T) h) ≠ 1 := by
  rw [phiFixedL_chart0_value_eq_at_DT P hu h]
  have hinj := quotient_rat_injective P
  intro hc
  have hone : (Ideal.Quotient.mk P).comp (algebraMap ℚ (R n)) (Polynomial.eval 0 h) =
      (Ideal.Quotient.mk P).comp (algebraMap ℚ (R n)) 1 := by
    rw [RingHom.comp_apply, RingHom.comp_apply, map_one, map_one]
    simpa using hc
  exact h1 (hinj hone)

/-- **T-avoidance, full form (0/1 side)**. -/
theorem phiFixedL_T_avoid {n : Nat} {T : Finset ℚ}
    (P : Ideal (R n)) [P.IsPrime] (hu : psiChart0Coord n T ∈ P) {h : Polynomial ℚ}
    (h0 : Polynomial.eval 0 h ≠ 0) (h1 : Polynomial.eval 0 h ≠ 1) :
    Ideal.Quotient.mk P (Polynomial.aeval (psiChart0Coord n T) h) ≠ 0 ∧
      Ideal.Quotient.mk P (Polynomial.aeval (psiChart0Coord n T) h) ≠ 1 :=
  ⟨phiFixedL_T_avoid_zero P hu h0, phiFixedL_T_avoid_one P hu h1⟩

#print axioms isUnit_algebraMap_rat
#print axioms quotient_rat_injective
#print axioms phiFixedL_T_avoid_zero
#print axioms phiFixedL_T_avoid_one
#print axioms phiFixedL_T_avoid
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiPhiTAvoidActual