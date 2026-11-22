import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace LeanFormal.IUT.XiFPaper.S2763SL2ClosureActual

abbrev F5 := ZMod 5
abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) F5
abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) F5

/-- The order-4 rotation matrix S = [[0,-1],[1,0]] in SL2(F5). -/
def S : SL2 :=
  ⟨!![0, -1; 1, 0], by decide⟩

/-- The order-5 unipotent matrix T = [[1,1],[0,1]] in SL2(F5). -/
def T : SL2 :=
  ⟨!![1, 1; 0, 1], by decide⟩

/-- The four letters S, T, S⁻¹, T⁻¹. -/
def letter (i : Fin 4) : SL2 := ![S, T, S⁻¹, T⁻¹] i

/-- Evaluate a word in the generators. -/
def evalWord : List (Fin 4) → SL2
  | [] => 1
  | i :: w => letter i * evalWord w

/-- Every evaluated word lies in the closure of S and T. -/
theorem evalWord_mem : ∀ w : List (Fin 4),
    evalWord w ∈ Subgroup.closure ({S, T} : Set SL2)
  | [] => Subgroup.one_mem _
  | i :: w => by
      have hi : letter i ∈ Subgroup.closure ({S, T} : Set SL2) := by
        fin_cases i
        · exact Subgroup.subset_closure (by simp [letter])
        · exact Subgroup.subset_closure (by simp [letter])
        · exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp [letter]))
        · exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp [letter]))
      exact Subgroup.mul_mem _ hi (evalWord_mem w)

/-- BFS word list for all 120 elements of SL2(F5). -/
def words : List (List (Fin 4)) :=
  [[],
   [0],
   [1],
   [2],
   [3],
   [0, 0],
   [0, 1],
   [0, 3],
   [1, 0],
   [1, 1],
   [1, 2],
   [2, 1],
   [2, 3],
   [3, 0],
   [3, 2],
   [3, 3],
   [0, 0, 1],
   [0, 0, 3],
   [0, 1, 0],
   [0, 1, 1],
   [0, 1, 2],
   [0, 3, 0],
   [0, 3, 2],
   [0, 3, 3],
   [1, 0, 3],
   [1, 1, 0],
   [1, 1, 2],
   [1, 2, 3],
   [2, 1, 1],
   [2, 3, 3],
   [3, 0, 1],
   [3, 2, 1],
   [3, 3, 0],
   [3, 3, 2],
   [0, 0, 1, 1],
   [0, 0, 3, 3],
   [0, 1, 0, 3],
   [0, 1, 1, 0],
   [0, 1, 1, 2],
   [0, 1, 2, 3],
   [0, 3, 0, 1],
   [0, 3, 2, 1],
   [0, 3, 3, 0],
   [0, 3, 3, 2],
   [1, 0, 3, 0],
   [1, 0, 3, 2],
   [1, 0, 3, 3],
   [1, 1, 0, 3],
   [1, 1, 2, 3],
   [1, 2, 3, 3],
   [3, 0, 1, 0],
   [3, 0, 1, 1],
   [3, 0, 1, 2],
   [3, 2, 1, 1],
   [3, 3, 0, 1],
   [3, 3, 2, 1],
   [0, 1, 0, 3, 0],
   [0, 1, 0, 3, 2],
   [0, 1, 1, 0, 3],
   [0, 1, 1, 2, 3],
   [0, 3, 0, 1, 0],
   [0, 3, 0, 1, 2],
   [0, 3, 3, 0, 1],
   [0, 3, 3, 2, 1],
   [1, 0, 3, 0, 1],
   [1, 0, 3, 2, 1],
   [1, 0, 3, 3, 0],
   [1, 0, 3, 3, 2],
   [1, 1, 0, 3, 3],
   [1, 1, 2, 3, 3],
   [3, 0, 1, 0, 3],
   [3, 0, 1, 1, 0],
   [3, 0, 1, 1, 2],
   [3, 0, 1, 2, 3],
   [3, 3, 0, 1, 1],
   [3, 3, 2, 1, 1],
   [0, 1, 0, 3, 0, 1],
   [0, 1, 0, 3, 2, 1],
   [0, 1, 1, 0, 3, 3],
   [0, 1, 1, 2, 3, 3],
   [0, 3, 0, 1, 0, 3],
   [0, 3, 0, 1, 2, 3],
   [0, 3, 3, 0, 1, 1],
   [0, 3, 3, 2, 1, 1],
   [1, 0, 3, 0, 1, 0],
   [1, 0, 3, 0, 1, 2],
   [1, 0, 3, 3, 0, 1],
   [1, 0, 3, 3, 2, 1],
   [1, 1, 0, 3, 3, 0],
   [1, 1, 0, 3, 3, 2],
   [3, 0, 1, 0, 3, 0],
   [3, 0, 1, 0, 3, 2],
   [3, 0, 1, 1, 0, 3],
   [3, 0, 1, 1, 2, 3],
   [3, 3, 0, 1, 1, 0],
   [3, 3, 0, 1, 1, 2],
   [0, 1, 1, 0, 3, 3, 0],
   [0, 1, 1, 0, 3, 3, 2],
   [0, 3, 3, 0, 1, 1, 0],
   [0, 3, 3, 0, 1, 1, 2],
   [1, 0, 3, 0, 1, 0, 3],
   [1, 0, 3, 0, 1, 2, 3],
   [1, 0, 3, 3, 0, 1, 1],
   [1, 0, 3, 3, 2, 1, 1],
   [1, 1, 0, 3, 3, 0, 1],
   [1, 1, 0, 3, 3, 2, 1],
   [3, 0, 1, 0, 3, 0, 1],
   [3, 0, 1, 0, 3, 2, 1],
   [3, 0, 1, 1, 0, 3, 3],
   [3, 0, 1, 1, 2, 3, 3],
   [3, 3, 0, 1, 1, 0, 3],
   [3, 3, 0, 1, 1, 2, 3],
   [0, 1, 1, 0, 3, 3, 0, 1],
   [0, 1, 1, 0, 3, 3, 2, 1],
   [0, 3, 3, 0, 1, 1, 0, 3],
   [0, 3, 3, 0, 1, 1, 2, 3],
   [1, 1, 0, 3, 3, 0, 1, 1],
   [1, 1, 0, 3, 3, 2, 1, 1],
   [0, 1, 1, 0, 3, 3, 0, 1, 1],
   [0, 1, 1, 0, 3, 3, 2, 1, 1]]

/-- The word list evaluates onto all of SL2(F5) (finite check). -/
theorem S2763_coverage :
    (words.map evalWord).toFinset = (Finset.univ : Finset SL2) := by
  decide

/-- S and T generate SL2(F5). -/
theorem S2763_closure_eq_top :
    Subgroup.closure ({S, T} : Set SL2) = ⊤ := by
  apply le_antisymm
  · exact le_top
  · intro g hg
    have hcov : g ∈ (words.map evalWord).toFinset := by
      rw [S2763_coverage]
      exact Finset.mem_univ g
    have hcov' : g ∈ words.map evalWord := by simpa using hcov
    rcases List.mem_map.mp hcov' with ⟨w, hw, rfl⟩
    exact evalWord_mem w

/-- The images in GL2(F5) generate the image of SL2(F5). -/
theorem S2763_map_closure_eq :
    Subgroup.map Matrix.SpecialLinearGroup.toGL
        (Subgroup.closure ({S, T} : Set SL2)) =
      Subgroup.closure ({Matrix.SpecialLinearGroup.toGL S,
        Matrix.SpecialLinearGroup.toGL T} : Set GL2) := by
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, rfl | rfl, rfl⟩ <;> simp
  · rintro (rfl | rfl)
    · exact ⟨S, by simp, rfl⟩
    · exact ⟨T, by simp, rfl⟩

/-- The GL2(F5) closure contains the image of SL2(F5). -/
theorem S2763_SL2_le_GL_closure :
    (⊤ : Subgroup SL2).map Matrix.SpecialLinearGroup.toGL ≤
      Subgroup.closure ({Matrix.SpecialLinearGroup.toGL S,
        Matrix.SpecialLinearGroup.toGL T} : Set GL2) := by
  rw [← S2763_map_closure_eq, S2763_closure_eq_top]

#check S
#check T
#check words
#check S2763_closure_eq_top
#check S2763_SL2_le_GL_closure
#print axioms S2763_closure_eq_top
#print axioms S2763_SL2_le_GL_closure

end LeanFormal.IUT.XiFPaper.S2763SL2ClosureActual
end
