import Mathlib
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S3108AdjoinRootSetAttempt

/-- The concrete prime label `l = 5` used by S1280. -/
abbrev fiveLabel : PrimeGeFive := S1280Five

/-- The actual Definition 3.1 field `F` from S1280. -/
abbrev F : Type := (S1280Arithmetic fiveLabel).F

local instance : Field F := (S1280Arithmetic fiveLabel).fieldF

/-- The Gaussian polynomial `X^2 + 1` over `F`. -/
def p : Polynomial F := Polynomial.X ^ 2 - Polynomial.C (-1)

/-- The actual root of `X^2 + 1` in `F[X]/(X^2+1)`. -/
def root : AdjoinRoot p := AdjoinRoot.root p

/-- The set of roots of `X^2 + 1` in `F[X]/(X^2+1)`. -/
def rootSet : Set (AdjoinRoot p) := {x | x ^ 2 = -1}

theorem mem_rootSet_iff (x : AdjoinRoot p) :
    x ∈ rootSet ↔ x ^ 2 = -1 :=
  Iff.rfl

theorem rootSet_eq : rootSet = {x : AdjoinRoot p | x ^ 2 = -1} :=
  rfl

/-- Conditional on `root^2 = -1`, the pair `{root, -root}` adjoins to `⊤`. -/
theorem adjoin_pair_eq (hroot : root ^ 2 = -1) :
    Algebra.adjoin F ({root, -root} : Set (AdjoinRoot p)) = ⊤ := by
  have hneg : -root = algebraMap F (AdjoinRoot p) (-1) * root := by
    simp
  have hpair :
      Algebra.adjoin F ({root, -root} : Set (AdjoinRoot p)) =
        Algebra.adjoin F ({root} : Set (AdjoinRoot p)) := by
    apply le_antisymm
    · rw [Algebra.adjoin_le_iff]
      intro x hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Algebra.subset_adjoin (by simp)
      · rw [hneg]
        exact Subalgebra.mul_mem _
          (Subalgebra.algebraMap_mem _ _)
          (Algebra.subset_adjoin (by simp))
    · rw [Algebra.adjoin_le_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Algebra.subset_adjoin (by simp)
  rw [hpair]
  exact AdjoinRoot.adjoinRoot_eq_top

/-- Conditional version: the adjoin of all roots of `X^2+1` is top. -/
theorem adjoin_rootSet_eq_top (hroot : root ^ 2 = -1) :
    Algebra.adjoin F (rootSet : Set (AdjoinRoot p)) = ⊤ := by
  apply le_antisymm le_top
  rw [← AdjoinRoot.adjoinRoot_eq_top]
  apply Algebra.adjoin_mono
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact hroot

#check mem_rootSet_iff
#check rootSet_eq
#check adjoin_pair_eq
#check adjoin_rootSet_eq_top

end LeanFormal.IUT.XiFPaper.S3108AdjoinRootSetAttempt
end
