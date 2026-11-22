/- Route 7.2 step 4: conjugate separation from a lower bound on the derivative at a root.
For a monic splitting polynomial whose roots all lie in the unit ball, the norm of the
derivative at a root x is at most the distance from x to any other root. -/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1UniversalSeparationActual

open Polynomial

variable {R : Type*} [NormedField R] [IsUltrametricDist R] [DecidableEq R]

/-- Norm of a multiset product in a normed field. -/
theorem norm_multiset_prod_eq (m : Multiset R) :
    ‖m.prod‖ = (m.map fun x => ‖x‖).prod := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, norm_mul, ih]

theorem multiset_prod_nonneg {m : Multiset ℝ} (h : ∀ x ∈ m, 0 ≤ x) : 0 ≤ m.prod := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.prod_cons]
      exact mul_nonneg (h a (Multiset.mem_cons_self a s))
        (ih (fun x hx => h x (Multiset.mem_cons_of_mem hx)))

theorem multiset_prod_le_one_of_forall_mem {m : Multiset ℝ}
    (h : ∀ x ∈ m, 0 ≤ x ∧ x ≤ 1) : m.prod ≤ 1 := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.prod_cons]
      have ha := h a (Multiset.mem_cons_self a s)
      have hs : s.prod ≤ 1 := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
      have hs0 : 0 ≤ s.prod := multiset_prod_nonneg (fun x hx => (h x (Multiset.mem_cons_of_mem hx)).1)
      nlinarith [ha.1, ha.2, hs, hs0]

theorem multiset_prod_le_of_mem {m : Multiset ℝ} (h0 : ∀ x ∈ m, 0 ≤ x)
    (h1 : ∀ x ∈ m, x ≤ 1) {a : ℝ} (ha : a ∈ m) : m.prod ≤ a := by
  rw [← Multiset.cons_erase ha]
  rw [Multiset.prod_cons]
  have hrest0 : 0 ≤ (m.erase a).prod :=
    multiset_prod_nonneg (fun x hx => h0 x (Multiset.mem_of_mem_erase hx))
  have hrest1 : (m.erase a).prod ≤ 1 :=
    multiset_prod_le_one_of_forall_mem
      (fun x hx => ⟨h0 x (Multiset.mem_of_mem_erase hx), h1 x (Multiset.mem_of_mem_erase hx)⟩)
  have ha0 : 0 ≤ a := h0 a ha
  nlinarith

/-- Route 7.2 step 4 (conjugate separation): for a monic splitting polynomial whose roots
all lie in the unit ball, the derivative at a root is bounded by the distance to every other
root. -/
theorem norm_eval_derivative_le_norm_sub {f : R[X]} (hm : f.Monic) (hf : f.Splits) {x x' : R}
    (hx : x ∈ f.roots) (hx' : x' ∈ f.roots) (hxx' : x' ≠ x)
    (hroot : ∀ a ∈ f.roots, ‖x - a‖ ≤ 1) :
    ‖Polynomial.eval x f.derivative‖ ≤ ‖x - x'‖ := by
  rw [hf.eval_root_derivative hm hx, norm_multiset_prod_eq, Multiset.map_map]
  simp only [Function.comp_def]
  set s := f.roots.erase x
  change (s.map (fun b => ‖x - b‖)).prod ≤ ‖x - x'‖
  have hmem : x' ∈ s := by
    rw [show s = f.roots.erase x from rfl]
    exact (Multiset.mem_erase_of_ne hxx').mpr hx'
  have h0 : ∀ a ∈ s.map (fun b => ‖x - b‖), (0 : ℝ) ≤ a := by
    intro a ha
    obtain ⟨b, _, rfl⟩ := Multiset.mem_map.mp ha
    exact norm_nonneg _
  have h1 : ∀ a ∈ s.map (fun b => ‖x - b‖), a ≤ 1 := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp ha
    exact hroot b (Multiset.mem_of_mem_erase hb)
  have ha : ‖x - x'‖ ∈ s.map (fun b => ‖x - b‖) :=
    Multiset.mem_map.mpr ⟨x', hmem, rfl⟩
  exact multiset_prod_le_of_mem h0 h1 ha

/-- Version with an explicit epsilon: if eps is a lower bound for the derivative at x, then
every other root is at distance at least eps from x. -/
theorem le_norm_sub_of_le_norm_eval_derivative {f : R[X]} (hm : f.Monic) (hf : f.Splits)
    {x x' : R} (hx : x ∈ f.roots) (hx' : x' ∈ f.roots) (hxx' : x' ≠ x)
    (hroot : ∀ a ∈ f.roots, ‖x - a‖ ≤ 1) {eps : ℝ}
    (heps : eps ≤ ‖Polynomial.eval x f.derivative‖) :
    eps ≤ ‖x - x'‖ :=
  le_trans heps (norm_eval_derivative_le_norm_sub hm hf hx hx' hxx' hroot)

#print axioms norm_eval_derivative_le_norm_sub
#print axioms le_norm_sub_of_le_norm_eval_derivative
end LeanFormal.IUT.XiFPaper.Mzk1G1UniversalSeparationActual
