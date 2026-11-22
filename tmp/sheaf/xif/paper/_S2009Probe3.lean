/-
S2009 probe 3: the pair action of GL_2(F_5).
-/
import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.OrderOfElement

noncomputable section
open Matrix

namespace S2009Probe3

abbrev K5 := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
abbrev GL2 := GL (Fin 2) K5
abbrev V2 := Fin 2 → K5

abbrev IsRep (v : V2) : Prop :=
  (v 0 = 1 ∨ v 0 = 2) ∨ (v 0 = 0 ∧ (v 1 = 1 ∨ v 1 = 2))

abbrev PairRep := {v : V2 // IsRep v}

def normSign (v : V2) : K5 :=
  if v 0 = 1 ∨ v 0 = 2 then 1
  else if v 0 = 3 ∨ v 0 = 4 then -1
  else if v 1 = 1 ∨ v 1 = 2 then 1
  else -1

def normalize (v : V2) : V2 := normSign v • v

theorem normalize_isRep : ∀ v : V2, v ≠ 0 → IsRep (normalize v) := by decide
theorem normalize_eq_or_neg : ∀ v : V2, normalize v = v ∨ normalize v = -v := by decide
theorem normalize_neg : ∀ v : V2, normalize (-v) = normalize v := by decide
theorem normalize_of_isRep : ∀ v : V2, IsRep v → normalize v = v := by decide
theorem isRep_ne_zero : ∀ v : V2, IsRep v → v ≠ 0 := by decide
theorem card_pairRep : Fintype.card PairRep = 12 := by decide

theorem smul_eq_zero_iff (g : GL2) (v : V2) : g • v = 0 ↔ v = 0 := by
  constructor
  · intro h
    exact Matrix.eq_zero_of_mulVec_eq_zero (Matrix.GeneralLinearGroup.det_ne_zero g) h
  · intro h
    rw [h]
    simp

def pairAct (g : GL2) (x : PairRep) : PairRep :=
  ⟨normalize (g • x.1), normalize_isRep (g • x.1) (by
    intro h
    exact isRep_ne_zero x.1 x.2 ((smul_eq_zero_iff g x.1).mp h))⟩

theorem pairAct_one (x : PairRep) : pairAct 1 x = x := by
  apply Subtype.ext
  show normalize (1 • x.1) = x.1
  rw [one_smul, normalize_of_isRep x.1 x.2]

theorem normalize_smul_congr (g : GL2) {v w : V2} (h : w = v ∨ w = -v) :
    normalize (g • w) = normalize (g • v) := by
  rcases h with rfl | rfl
  · rfl
  · rw [show g • (-v) = -(g • v) by simp, normalize_neg]

theorem pairAct_mul (g h : GL2) (x : PairRep) :
    pairAct (g * h) x = pairAct g (pairAct h x) := by
  apply Subtype.ext
  show normalize ((g * h) • x.1) = normalize (g • normalize (h • x.1))
  rw [mul_smul]
  exact (normalize_smul_congr g (normalize_eq_or_neg (h • x.1))).symm

end S2009Probe3
