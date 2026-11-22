import Iut.Foundations.Frobenioid
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
/-! # S423: the natural-number DivisorialAddMonoid
Carrier ℕ, integral via Nat.add_left_cancel, sharp because the only additive
unit in ℕ is 0, and saturated via the explicit GrothendieckAddGroup ℕ
representation AddLocalization.mk.  No divisorial instance is asserted without
proof. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
namespace LeanFormal.IUT.XiFPaper.S423NatDivisorialAddMonoidActual
open Iut
/-- The additive monoid ℕ as a sharp integral saturated divisorial monoid. -/
noncomputable def natDivisorialAddMonoid : Iut.DivisorialAddMonoid where
  carrier := ℕ
  integral := by
    intro a b c h
    exact Nat.add_left_cancel h
  sharp := by
    intro a ha
    rcases ha with ⟨u, hu⟩
    -- every additive unit of ℕ is zero
    have hunit : (u : ℕ) + (u.neg : ℕ) = 0 := AddUnits.add_neg u
    have hzero : (u : ℕ) = 0 := by omega
    omega
  saturated := by
    intro x n hx
    rcases hx with ⟨m, hm⟩
    -- represent x by a localization class mk a b
    revert hm
    refine AddLocalization.induction_on x ?_
    intro y
    obtain ⟨a, b⟩ := y
    intro hm
    -- hm : n • mk a b = of m = mk m 0
    rw [AddLocalization.mk_nsmul] at hm
    rw [show Algebra.GrothendieckAddGroup.of m =
        AddLocalization.mk m (0 : (⊤ : AddSubmonoid ℕ)) by rfl] at hm
    have hrel := AddLocalization.mk_eq_mk_iff'.mp hm
    have hrel' : n.1 • (b : ℕ) + m = n.1 • a := by
      simpa using hrel
    have hna : n.1 * (b : ℕ) + m = n.1 * a := by
      simpa [nsmul_eq_mul] using hrel'
    have hb_le_a : (b : ℕ) ≤ a := by
      have hle : n.1 * (b : ℕ) ≤ n.1 * a := by omega
      exact Nat.le_of_mul_le_mul_left hle n.pos
    refine ⟨a - (b : ℕ), ?_⟩
    rw [show Algebra.GrothendieckAddGroup.of (a - (b : ℕ)) =
        AddLocalization.mk (a - (b : ℕ)) (0 : (⊤ : AddSubmonoid ℕ)) by rfl]
    rw [AddLocalization.mk_eq_mk_iff']
    change (b : ℕ) + (a - (b : ℕ)) = (0 : ℕ) + a
    omega
end LeanFormal.IUT.XiFPaper.S423NatDivisorialAddMonoidActual
