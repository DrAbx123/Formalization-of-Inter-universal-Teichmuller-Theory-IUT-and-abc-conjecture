import tmp.sheaf.xif.paper.S1720SourceArithmeticActual
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic

noncomputable section
open Polynomial

namespace ProbeKernel

open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual

abbrev F := S1720Field

theorem S1687P_ne_zero' : S1687P ≠ 0 := by
  intro h
  have hdeg : S1687P.natDegree = 3 := by unfold S1687P; compute_degree!
  rw [h, Polynomial.natDegree_zero] at hdeg
  norm_num at hdeg

noncomputable def r (c : S1687P.rootSet F) : F :=
  Classical.choose (by
    sorry : ∃ r : F, r ^ 2 = (c : F))

theorem r_sq (c : S1687P.rootSet F) : (r c) ^ 2 = (c : F) :=
  Classical.choose_spec (by
    sorry : ∃ r : F, r ^ 2 = (c : F))

noncomputable def iroot : F := Classical.choose S1720HasSqrtNegOne

theorem iroot_sq : iroot ^ 2 = (-1 : F) := by
  have h : iroot * iroot = -1 := Classical.choose_spec S1720HasSqrtNegOne
  rw [sq]
  exact h

theorem S1720SqrtPolynomial_ne_zero' : S1720SqrtPolynomial ≠ 0 := by
  unfold S1720SqrtPolynomial
  intro h
  have h0 := congrArg (fun p : ℚ[X] => p.coeff 0) h
  simp at h0

theorem S1720H_ne_zero' : S1720H ≠ 0 := by
  unfold S1720H
  exact mul_ne_zero S1687H_ne_zero S1720SqrtPolynomial_ne_zero'

example {x : F} (hx : x ∈ S1720H.rootSet F) :
    (∃ c : S1687P.rootSet F, x = r c ∨ x = - r c) ∨ x = iroot ∨ x = -iroot := by
  have hx_eval : aeval x S1720H = 0 :=
    (Polynomial.mem_rootSet_of_ne S1720H_ne_zero').mp hx
  have hx_eval' : aeval x (S1687H * S1720SqrtPolynomial) = 0 := by
    simpa [S1720H] using hx_eval
  rw [Polynomial.aeval_mul (R := ℚ) (x := x)] at hx_eval'
  rcases mul_eq_zero.mp hx_eval' with hH | hI
  · left
    have hx2 : aeval (x ^ 2) S1687P = 0 := by
      rw [← S1687H_eval_eq]
      exact hH
    have hx2mem : x ^ 2 ∈ S1687P.rootSet F :=
      (Polynomial.mem_rootSet_of_ne S1687P_ne_zero').mpr hx2
    let c : S1687P.rootSet F := ⟨x ^ 2, hx2mem⟩
    refine ⟨c, ?_⟩
    have hc : (c : F) = x ^ 2 := rfl
    have hsq : x ^ 2 = (r c) ^ 2 := by rw [← hc, r_sq c]
    exact eq_or_eq_neg_of_sq_eq_sq x (r c) hsq
  · right
    have hx2 : x ^ 2 = (-1 : F) := by
      have h : aeval x S1720SqrtPolynomial = 0 := hI
      unfold S1720SqrtPolynomial at h
      simp only [map_add, map_pow, aeval_X, aeval_one] at h
      linear_combination h
    have hsq : x ^ 2 = iroot ^ 2 := by rw [hx2, iroot_sq]
    exact eq_or_eq_neg_of_sq_eq_sq x iroot hsq

end ProbeKernel
