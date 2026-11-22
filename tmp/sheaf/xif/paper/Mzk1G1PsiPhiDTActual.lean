/- B1 value-level facts: at the protected points `u = 0` the chart-0 map
`lambda |-> h(u)` of `phiFixedL` takes the constant value `h(0)`; hence T-avoidance
reduces to `h(0) notin {0,1}`. Route B2/B1 (L273-278, §4.3). -/
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyLambdaFactsActual
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiPhiDTActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual

/-- If `u` lies in an ideal `P`, then `h(u) - h(0)` lies in `P`: the difference is
`u` times a polynomial evaluated at `u`. -/
theorem aeval_sub_algebraMap_eval_zero_mem {R : Type} [CommRing R] [Algebra ℚ R]
    (P : Ideal R) (u : R) (hu : u ∈ P) (h : Polynomial ℚ) :
    Polynomial.aeval u h - algebraMap ℚ R (Polynomial.eval 0 h) ∈ P := by
  have hdvd : Polynomial.X ∣ h - Polynomial.C (Polynomial.eval 0 h) := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_sub, Polynomial.coeff_C_zero,
      ← Polynomial.coeff_zero_eq_eval_zero]
    ring
  obtain ⟨g, hg⟩ := hdvd
  have hsub : Polynomial.aeval u h - algebraMap ℚ R (Polynomial.eval 0 h) =
      Polynomial.aeval u g * u := by
    have h1 : Polynomial.aeval u (h - Polynomial.C (Polynomial.eval 0 h)) =
        Polynomial.aeval u g * u := by
      rw [hg]
      simp only [Polynomial.aeval_X, Polynomial.aeval_mul, Polynomial.aeval_C, mul_comm]
    simpa [map_sub] using h1
  rw [hsub]
  exact Ideal.mul_mem_left P (Polynomial.aeval u g) hu


/-- Specialisation to the Fermat chart ring: the difference between the value `h(u)` at a
prime containing the protected coordinate `u` and the constant `h(0)` lies in the prime. -/
theorem phiFixedL_chart0_value_sub_at_DT {n : Nat} {T : Finset ℚ}
    (P : Ideal (R n)) (hu : psiChart0Coord n T ∈ P) (h : Polynomial ℚ) :
    Polynomial.aeval (psiChart0Coord n T) h - algebraMap ℚ (R n) (Polynomial.eval 0 h) ∈ P :=
  aeval_sub_algebraMap_eval_zero_mem P (psiChart0Coord n T) hu h

/-- The value of `h(u)` at a point with `u = 0` equals the constant `h(0)` modulo the
prime: `h(u) - h(0) = 0` in the quotient. -/
theorem phiFixedL_chart0_value_eq_at_DT {n : Nat} {T : Finset ℚ}
    (P : Ideal (R n)) (hu : psiChart0Coord n T ∈ P) (h : Polynomial ℚ) :
    Ideal.Quotient.mk P (Polynomial.aeval (psiChart0Coord n T) h) =
      Ideal.Quotient.mk P (algebraMap ℚ (R n) (Polynomial.eval 0 h)) :=
  Ideal.Quotient.eq.mpr (phiFixedL_chart0_value_sub_at_DT P hu h)

#print axioms aeval_sub_algebraMap_eval_zero_mem
#print axioms phiFixedL_chart0_value_sub_at_DT
#print axioms phiFixedL_chart0_value_eq_at_DT
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiPhiDTActual
