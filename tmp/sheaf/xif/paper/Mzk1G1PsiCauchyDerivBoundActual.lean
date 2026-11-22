/- B1 analytic h (kurt): isolated derivative root bound (split from CauchyBound3 to
decouple compilation). Depends only on CauchyBoundActual. Default heartbeats.
-/
import tmp.sheaf.xif.paper.Mzk1G1PsiCauchyBoundActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators NNReal

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiCauchyDerivBoundActual

open Polynomial

theorem derivative_root_bound_choose (p : ℂ[X]) (hp : p.Monic)
    (hroots : ∀ z ∈ p.roots, ‖z‖ ≤ 1) {z : ℂ}
    (hz : p.derivative.IsRoot z) (hd : 1 ≤ p.natDegree) :
    ‖z‖ ≤ 1 + (p.natDegree : ℝ) * 2 ^ p.natDegree := by
  have hder : p.derivative ≠ 0 := by
    rw [Polynomial.derivative_ne_zero]
    omega
  have hlt : ‖z‖₊ < Polynomial.cauchyBound p.derivative :=
    Polynomial.IsRoot.norm_lt_cauchyBound hder hz
  have hB : ((p.natDegree : ℝ≥0) * 2 ^ p.natDegree) = ((p.natDegree : ℝ) * (2 : ℝ) ^ p.natDegree : ℝ≥0) := by
    push_cast
    rfl
  have hcoeff : ∀ i, ‖p.derivative.coeff i‖₊ ≤
      ((p.natDegree : ℝ≥0) * 2 ^ p.natDegree) := by
    intro i
    by_cases hi : i + 1 ≤ p.natDegree
    · have hstep : p.derivative.coeff i = (i + 1) * p.coeff (i + 1) := by
        rw [Polynomial.coeff_derivative]
        push_cast
        ring
      rw [hstep, nnnorm_mul]
      have h1 : ‖p.coeff (i + 1)‖₊ ≤ (2 : ℝ≥0) ^ p.natDegree := by
        have h2 : ‖p.coeff (i + 1)‖ ≤ 2 ^ p.natDegree :=
          (coeff_norm_le_choose p hp hroots (i + 1)).trans
            (choose_le_two_pow p.natDegree (i + 1))
        exact_mod_cast h2
      have h2 : ‖((i + 1 : ℕ) : ℂ)‖₊ ≤ (p.natDegree : ℝ≥0) := by
        rw [nnnorm_complex_natCast]
        exact_mod_cast Nat.le_of_succ_le hi
      exact mul_le_mul h2 h1 (zero_le _) (zero_le _)
    · have hzero : p.derivative.coeff i = 0 := by
        rw [Polynomial.coeff_derivative]
        have : p.coeff (i + 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_le hi)
        rw [this, mul_zero]
      rw [hzero]
      simp
  have hsup : (Finset.range p.derivative.natDegree).sup
      (fun i => ‖p.derivative.coeff i‖₊) ≤ ((p.natDegree : ℝ≥0) * 2 ^ p.natDegree) :=
    Finset.sup_le (fun i _ => hcoeff i)
  have hlead : (1 : ℝ≥0) ≤ ‖p.derivative.leadingCoeff‖₊ := by
    rw [Polynomial.leadingCoeff_derivative, hp.leadingCoeff, one_mul,
      nnnorm_complex_natCast]
    exact_mod_cast hd
  have hcb : Polynomial.cauchyBound p.derivative ≤
      ((p.natDegree : ℝ≥0) * 2 ^ p.natDegree) + 1 := by
    unfold Polynomial.cauchyBound
    have hdiv : (Finset.range p.derivative.natDegree).sup
        (fun i => ‖p.derivative.coeff i‖₊) / ‖p.derivative.leadingCoeff‖₊ ≤
        (Finset.range p.derivative.natDegree).sup (fun i => ‖p.derivative.coeff i‖₊) :=
      div_le_self (a := (Finset.range p.derivative.natDegree).sup
        (fun i => ‖p.derivative.coeff i‖₊)) (zero_le _) hlead
    exact add_le_add_right (hdiv.trans hsup) 1
  have hle : ‖z‖₊ ≤ ((p.natDegree : ℝ≥0) * 2 ^ p.natDegree) + 1 :=
    le_of_lt (lt_of_lt_of_le hlt hcb)
  have hcast : (((p.natDegree : ℝ≥0) * 2 ^ p.natDegree) + 1 : ℝ≥0) =
      (1 : ℝ) + (p.natDegree : ℝ) * (2 : ℝ) ^ p.natDegree := by
    push_cast
    ring
  have hle' : (‖z‖₊ : ℝ) ≤ ((((p.natDegree : ℝ≥0) * 2 ^ p.natDegree) + 1 : ℝ≥0) : ℝ) := by
    exact_mod_cast hle
  have hnorm : ‖z‖ = (‖z‖₊ : ℝ) := by
    simpa using (coe_nnnorm z).symm
  rw [hnorm]
  rwa [hcast] at hle'


#print axioms derivative_root_bound_choose

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiCauchyDerivBoundActual
end