import tmp.sheaf.xif.paper.S2481QiGaloisActual
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Perfect
noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2482QiGaloisDoneActual
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2481QiGaloisActual
def S2482root : F := AdjoinRoot.root (X ^ 2 + 1 : ℚ[X])
theorem S2482root_sq : S2482root ^ 2 = -1 := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 + 1 : ℚ[X])
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_one] at h
  change AdjoinRoot.root (X ^ 2 + 1 : ℚ[X]) ^ 2 = -1
  linear_combination h
theorem S2482map_eq :
    ((X ^ 2 + 1 : ℚ[X]).map (algebraMap ℚ F)) =
      (X - C S2482root) * (X + C S2482root) := by
  rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_one,
    Polynomial.map_X]
  calc
    X ^ 2 + 1 = X ^ 2 - C (-1) := by norm_num
    _ = X ^ 2 - C (S2482root ^ 2) := by rw [S2482root_sq]
    _ = (X - C S2482root) * (X + C S2482root) := by
      rw [show C (S2482root ^ 2) = C S2482root ^ 2 by rw [map_pow]]
      ring
theorem S2482splits :
    Polynomial.Splits ((X ^ 2 + 1 : ℚ[X]).map (algebraMap ℚ F)) := by
  rw [S2482map_eq]
  exact (Polynomial.Splits.X_sub_C S2482root).mul (Polynomial.Splits.X_add_C S2482root)
theorem S2482root_mem_rootSet :
    S2482root ∈ (X ^ 2 + 1 : ℚ[X]).rootSet F := by
  rw [Polynomial.mem_rootSet']
  constructor
  · rw [S2482map_eq]
    exact mul_ne_zero (Polynomial.X_sub_C_ne_zero _) (Polynomial.X_add_C_ne_zero _)
  · simp [Polynomial.aeval_def, S2482root_sq]
theorem S2482rootSet_subset :
    ((X ^ 2 + 1 : ℚ[X]).rootSet F) ⊆ ({S2482root, -S2482root} : Set F) := by
  intro x hx
  rw [Polynomial.mem_rootSet'] at hx
  obtain ⟨_, hx0⟩ := hx
  have hx_sq : x ^ 2 = -1 := by
    have hx1 : x ^ 2 + 1 = 0 := by simpa using hx0
    linear_combination hx1
  have hfac : (x - S2482root) * (x + S2482root) = 0 := by
    have h : x ^ 2 - S2482root ^ 2 = 0 := by
      rw [hx_sq, S2482root_sq]
      ring
    rw [show (x - S2482root) * (x + S2482root) = x ^ 2 - S2482root ^ 2 by ring]
    exact h
  rcases mul_eq_zero.mp hfac with h | h
  · left
    exact sub_eq_zero.mp h
  · right
    exact eq_neg_of_add_eq_zero_left h
theorem S2482adjoin_rootSet :
    Algebra.adjoin ℚ ((X ^ 2 + 1 : ℚ[X]).rootSet F) = ⊤ := by
  have hle1 : Algebra.adjoin ℚ ({S2482root} : Set F) ≤
      Algebra.adjoin ℚ ((X ^ 2 + 1 : ℚ[X]).rootSet F) :=
    Algebra.adjoin_le (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact Algebra.subset_adjoin S2482root_mem_rootSet)
  have hle2 : Algebra.adjoin ℚ ((X ^ 2 + 1 : ℚ[X]).rootSet F) ≤
      Algebra.adjoin ℚ ({S2482root} : Set F) :=
    Algebra.adjoin_le (by
      intro x hx
      rcases S2482rootSet_subset hx with hx' | hx'
      · rw [hx']; exact Algebra.self_mem_adjoin_singleton ℚ S2482root
      · rw [hx']; exact neg_mem (Algebra.self_mem_adjoin_singleton ℚ S2482root))
  have hEq : Algebra.adjoin ℚ ((X ^ 2 + 1 : ℚ[X]).rootSet F) =
      Algebra.adjoin ℚ ({S2482root} : Set F) :=
    le_antisymm hle2 hle1
  rw [hEq]
  change Algebra.adjoin ℚ
    ({AdjoinRoot.root (X ^ 2 + 1 : ℚ[X])} :
      Set (AdjoinRoot (X ^ 2 + 1 : ℚ[X]))) = ⊤
  exact AdjoinRoot.adjoinRoot_eq_top (R := ℚ) (f := (X ^ 2 + 1 : ℚ[X]))
instance S2482IsSplittingField :
    Polynomial.IsSplittingField ℚ F (X ^ 2 + 1 : ℚ[X]) where
  splits' := S2482splits
  adjoin_rootSet' := S2482adjoin_rootSet
instance S2482IsGalois : IsGalois ℚ F :=
  IsGalois.of_separable_splitting_field (p := (X ^ 2 + 1 : ℚ[X]))
    (PerfectField.separable_of_irreducible S2480_irreducible)
#check S2482IsSplittingField
#check S2482IsGalois
#check S2482root
#check S2482root_sq
#check S2482map_eq
#check S2482splits
end LeanFormal.IUT.XiFPaper.S2482QiGaloisDoneActual
end
