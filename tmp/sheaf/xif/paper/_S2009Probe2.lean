/-
S2009 probe 2: the 12-pair model and normalization.
-/
import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.OrderOfElement

noncomputable section
open Matrix

namespace S2009Probe2

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

example : normalize ![3, 4] = ![2, 1] := by decide
example : normalize ![0, 4] = ![0, 1] := by decide

theorem normalize_isRep : ∀ v : V2, v ≠ 0 → IsRep (normalize v) := by
  decide

theorem normalize_eq_or_neg : ∀ v : V2, normalize v = v ∨ normalize v = -v := by
  decide

theorem normalize_neg : ∀ v : V2, normalize (-v) = normalize v := by
  decide

theorem normalize_of_isRep : ∀ v : V2, IsRep v → normalize v = v := by
  decide

end S2009Probe2
