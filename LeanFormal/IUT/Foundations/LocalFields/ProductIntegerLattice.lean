import LeanFormal.IUT.Foundations.LocalFields.FinitePadicIntegralLattice
import Mathlib.Analysis.Normed.Group.Ultra
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldProductHull

/-!
# The holomorphic integer region as an actual integral submodule

In a finite product of ultrametric local fields the existing holomorphic
unit region is a compact open Zp submodule. This is the integral reference
after an etale field decomposition; it is constructed independently of
the integral tensor lattice.
-/

namespace LeanFormal.IUT.LocalFieldProductHull

open LeanFormal.IUT.FinitePadicIntegralLattice
open scoped LeanFormal.IUT.FinitePadicIntegralLattice

noncomputable section

variable {p : ℕ} [Fact p.Prime] {J : Type*} {E : J → Type*}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
variable [∀ j, IsUltrametricDist (E j)]

def productIntegerLattice : Submodule ℤ_[p] ((j : J) → E j) where
  carrier := unitRegion (K := E)
  zero_mem' j := by simp
  add_mem' hx hy j := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx j) (hy j))
  smul_mem' z x hx j := by
    change ‖(z : ℚ_[p]) • x j‖ ≤ 1
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) z.property).trans (hx j)

theorem coe_productIntegerLattice :
    (productIntegerLattice (p := p) (E := E) : Set ((j : J) → E j)) = unitRegion := rfl

theorem isOpen_productIntegerLattice [Finite J] :
    IsOpen (productIntegerLattice (p := p) (E := E) : Set ((j : J) → E j)) := by
  have hopen (j : J) : IsOpen {x : E j | ‖x‖ ≤ 1} := by
    apply Metric.isOpen_iff.mpr
    intro x hx
    refine ⟨1, zero_lt_one, ?_⟩
    intro y hy
    have hsmall : ‖y - x‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
    change ‖y‖ ≤ 1
    calc
      ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ max ‖y - x‖ ‖x‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le hsmall.le hx
  have heq : (productIntegerLattice (p := p) (E := E) : Set ((j : J) → E j)) =
      Set.pi Set.univ (fun j => {x : E j | ‖x‖ ≤ 1}) := by
    ext x
    change (∀ j, ‖x j‖ ≤ 1) ↔ ∀ j ∈ Set.univ, ‖x j‖ ≤ 1
    simp only [Set.mem_univ, forall_const]
  rw [heq]
  exact isOpen_set_pi (Set.toFinite Set.univ) (fun j _ => hopen j)

theorem isCompact_productIntegerLattice [Finite J] [∀ j, ProperSpace (E j)] :
    IsCompact (productIntegerLattice (p := p) (E := E) : Set ((j : J) → E j)) :=
  isCompact_unitRegion

def productHullLattice (S : Set ((j : J) → E j)) : Submodule ℤ_[p] ((j : J) → E j) where
  carrier := hull S
  zero_mem' lam _ _ j := by
    change ‖(0 : E j)‖ ≤ ‖lam j‖
    simpa only [norm_zero] using norm_nonneg (lam j)
  add_mem' {x y} hx hy lam hnonzero hbound j := by
    change ‖x j + y j‖ ≤ ‖lam j‖
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (hx lam hnonzero hbound j) (hy lam hnonzero hbound j))
  smul_mem' z x hx lam hnonzero hbound j := by
    change ‖(z : ℚ_[p]) • x j‖ ≤ ‖lam j‖
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) z.property).trans
      (hx lam hnonzero hbound j)

theorem coe_productHullLattice (S : Set ((j : J) → E j)) :
    (productHullLattice (p := p) S : Set ((j : J) → E j)) = hull S := rfl

theorem integral_span_le_productHullLattice (S : Set ((j : J) → E j)) :
    Submodule.span ℤ_[p] S ≤ productHullLattice (p := p) S :=
  Submodule.span_le.mpr (subset_hull S)

end

end LeanFormal.IUT.LocalFieldProductHull
