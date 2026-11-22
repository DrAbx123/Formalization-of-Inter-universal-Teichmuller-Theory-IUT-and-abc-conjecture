import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod

noncomputable section
open Matrix
namespace S2009Probe9

abbrev K5 := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
abbrev V2 := Fin 2 → K5

abbrev IsRep (v : V2) : Prop :=
  (v 0 = 1 ∨ v 0 = 2) ∨ (v 0 = 0 ∧ (v 1 = 1 ∨ v 1 = 2))
abbrev PairRep := {v : V2 // IsRep v}

def repList : List PairRep :=
  [⟨![0, 1], by decide⟩,
   ⟨![1, 1], by decide⟩,
   ⟨![1, 2], by decide⟩,
   ⟨![2, 3], by decide⟩,
   ⟨![2, 0], by decide⟩,
   ⟨![0, 2], by decide⟩,
   ⟨![2, 2], by decide⟩,
   ⟨![2, 4], by decide⟩,
   ⟨![1, 4], by decide⟩,
   ⟨![1, 0], by decide⟩,
   ⟨![1, 3], by decide⟩,
   ⟨![2, 1], by decide⟩]

theorem repList_length : repList.length = 12 := by decide

def pairOf (i : Fin 12) : PairRep :=
  repList.get ⟨i.1, by rw [repList_length]; exact i.2⟩

theorem mem_repList : ∀ x : PairRep, x ∈ repList := by decide

def indexOf (x : PairRep) : Fin 12 :=
  ⟨repList.idxOf x, by
    have h := List.idxOf_lt_length_of_mem (mem_repList x)
    rwa [repList_length] at h⟩

theorem indexOf_pairOf : ∀ i : Fin 12, indexOf (pairOf i) = i := by decide
theorem pairOf_indexOf : ∀ x : PairRep, pairOf (indexOf x) = x := by decide

def pairEquivFin : PairRep ≃ Fin 12 where
  toFun := indexOf
  invFun := pairOf
  left_inv := pairOf_indexOf
  right_inv := indexOf_pairOf

#check pairEquivFin
example : pairEquivFin (pairOf 0) = 0 := by decide

end S2009Probe9