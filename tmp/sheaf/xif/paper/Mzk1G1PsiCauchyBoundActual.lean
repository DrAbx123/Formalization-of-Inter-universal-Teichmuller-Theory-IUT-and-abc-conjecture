/- B1 analytic h, batch 1 (kurt, for henry): product/root norm bounds over C.

Contents (unconditional, no new conditions):
* norm of a multiset product in C (NNReal form);
* the value of the monic split polynomial at a point in terms of its roots;
* norm_eval_prod_bound: monic split p with roots in the unit disc evaluated at a
  point of the unit disc has norm at most 2 ^ natDegree.

Default heartbeats (heartbeat-cleanup batch). -/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators NNReal NNReal

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiCauchyBoundActual

open Polynomial

/-- The NNReal norm of a multiset product in C is the product of the norms. -/
theorem nnnorm_multiset_prod_complex (s : Multiset ℂ) :
    ‖s.prod‖₊ = (s.map fun z => ‖z‖₊).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.prod_cons, nnnorm_mul, ih, Multiset.map_cons, Multiset.prod_cons]

/-- The value of the monic split polynomial at a point, as the product of the
root differences. -/
theorem prod_X_sub_C_eval (p : ℂ[X]) (hp : p.Monic)
    (hcard : p.roots.card = p.natDegree) (α : ℂ) :
    p.eval α = (p.roots.map fun r => α - r).prod := by
  have hprod : p = (p.roots.map fun r => Polynomial.X - Polynomial.C r).prod :=
    (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp hcard).symm
  conv_lhs => rw [hprod]
  rw [Polynomial.eval_multiset_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro r _
  simp

/-- Batch-1 evaluation bound: a monic polynomial over C with all roots in the
closed unit disc, evaluated at a point of the closed unit disc, has norm at most
2 ^ natDegree. -/
theorem norm_eval_prod_bound (p : ℂ[X]) (hp : p.Monic)
    (hroots : ∀ z ∈ p.roots, ‖z‖ ≤ 1) (α : ℂ) (hα : ‖α‖ ≤ 1) :
    ‖p.eval α‖ ≤ 2 ^ p.natDegree := by
  have hsplit : p.Splits := IsAlgClosed.splits p
  have hcard : p.roots.card = p.natDegree := hsplit.natDegree_eq_card_roots.symm
  have heval : p.eval α = (p.roots.map fun r => α - r).prod :=
    prod_X_sub_C_eval p hp hcard α
  rw [heval]
  have hnn : ‖(p.roots.map fun r => α - r).prod‖₊ =
      ((p.roots.map fun r => α - r).map fun z => ‖z‖₊).prod :=
    nnnorm_multiset_prod_complex _
  have hfac : ∀ r ∈ (p.roots.map fun r => α - r).map (fun z => ‖z‖₊), r ≤ (2 : ℝ≥0) := by
    intro r hr
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hr
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hz
    have hx1 : ‖x‖ ≤ 1 := hroots x hx
    have hdiff : ‖α - x‖ ≤ ‖α‖ + ‖x‖ := norm_sub_le _ _
    have h2 : ‖α - x‖ ≤ 2 := by linarith
    exact_mod_cast h2
  have hmain : ((p.roots.map fun r => α - r).map fun z => ‖z‖₊).prod ≤
      (2 : ℝ≥0) ^ p.natDegree := by
    refine (Multiset.prod_le_pow_card _ _ hfac).trans_eq ?_
    congr 1
    simp [hcard]
  have h2 : (‖(p.roots.map fun r => α - r).prod‖₊ : ℝ) ≤
      ((2 : ℝ≥0) ^ p.natDegree : ℝ) := by
    rw [hnn]
    exact_mod_cast hmain
  simpa [coe_nnnorm, NNReal.coe_pow] using h2

#print axioms nnnorm_multiset_prod_complex
#print axioms prod_X_sub_C_eval
#print axioms norm_eval_prod_bound

/-! ## Batch 2: Cauchy root bound via Mathlib Polynomial.cauchyBound -/

theorem cauchy_root_bound (p : ℂ[X]) (hp : p ≠ 0) (hmonic : p.Monic) (B : ℝ≥0)
    (hcoeff : ∀ i, ‖p.coeff i‖₊ ≤ B) {z : ℂ} (hz : p.IsRoot z) :
    ‖z‖ ≤ 1 + (B : ℝ) := by
  have hlt : ‖z‖₊ < Polynomial.cauchyBound p :=
    Polynomial.IsRoot.norm_lt_cauchyBound hp hz
  have hcb : Polynomial.cauchyBound p ≤ B + 1 := by
    unfold Polynomial.cauchyBound
    rw [hmonic.leadingCoeff, nnnorm_one, div_one]
    have hsup : (Finset.range p.natDegree).sup (fun i => ‖p.coeff i‖₊) ≤ B :=
      Finset.sup_le (fun i _ => hcoeff i)
    exact add_le_add_right hsup 1
  have hle : ‖z‖₊ ≤ B + 1 := le_of_lt (lt_of_lt_of_le hlt hcb)
  have hle' : (‖z‖₊ : ℝ) ≤ ((B + 1 : ℝ≥0) : ℝ) := by exact_mod_cast hle
  have hcast : ((B + 1 : ℝ≥0) : ℝ) = 1 + (B : ℝ) := by
    rw [NNReal.coe_add, NNReal.coe_one]; ring
  calc ‖z‖ = (‖z‖₊ : ℝ) := (coe_nnnorm z).symm
    _ ≤ ((B + 1 : ℝ≥0) : ℝ) := hle'
    _ = 1 + (B : ℝ) := hcast

#print axioms cauchy_root_bound

/-- Batch-3 support: roots of a monic derivative are bounded by 1 + B. -/
theorem derivative_root_bound (p : ℂ[X]) (hder : p.derivative ≠ 0)
    (hmonic : p.derivative.Monic) (B : ℝ≥0)
    (hcoeff : ∀ i, ‖p.derivative.coeff i‖₊ ≤ B) {z : ℂ}
    (hz : p.derivative.IsRoot z) : ‖z‖ ≤ 1 + B :=
  cauchy_root_bound p.derivative hder hmonic B hcoeff hz

#print axioms derivative_root_bound

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiCauchyBoundActual
end