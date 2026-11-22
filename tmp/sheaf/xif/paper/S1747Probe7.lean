import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Artinian.Module
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

open CategoryTheory
open scoped TensorProduct

universe u

namespace S1747Probe

section
variable {K Bm Ai Aj : Type} [Field K] [Field Bm] [Field Ai] [Field Aj]
  [Algebra K Bm] [Algebra K Ai] [Algebra K Aj]
  [Algebra Bm Ai] [Algebra Bm Aj] [IsScalarTower K Bm Ai] [IsScalarTower K Bm Aj]

example : True := by
  -- the tensor product, as a Bm-algebra
  let T := Ai ⊗[Bm] Aj
  haveI : CommRing T := inferInstance
  haveI : Algebra Bm T := inferInstance
  -- K-algebra structure by restriction of scalars along K -> Bm -> T
  letI : Algebra K T := (algebraMap Bm T).comp (algebraMap K Bm) |> RingHom.toAlgebra
  -- check compatibility of the algebraMap
  have hcomp : (algebraMap K T) = (algebraMap Bm T).comp (algebraMap K Bm) := rfl
  -- an element of the tensor as a K-algebra map from Ai
  let g : Ai →ₐ[K] T :=
    { toFun := fun x => x ⊗ₜ[Bm] 1
      map_one' := by simp
      map_mul' := by intro x y; simp
      map_zero' := by simp
      map_add' := by intro x y; simp
      commutes' := by
        intro k
        show (algebraMap K Ai k) ⊗ₜ[Bm] (1 : Aj) = algebraMap K T k
        rw [hcomp, RingHom.comp_apply, Algebra.algebraMap_eq_smul_one,
          Algebra.TensorProduct.algebraMap_apply]
        -- now both sides are tensor elements
        rw [Algebra.TensorProduct.algebraMap_apply]
        congr 1
        rw [IsScalarTower.algebraMap_apply K Bm Aj] }
  -- the right factor
  let h : Aj →ₐ[K] T :=
    { toFun := fun y => (1 : Ai) ⊗ₜ[Bm] y
      map_one' := by simp
      map_mul' := by intro x y; simp
      map_zero' := by simp
      map_add' := by intro x y; simp
      commutes' := by
        intro k
        show (1 : Ai) ⊗ₜ[Bm] (algebraMap K Aj k) = algebraMap K T k
        rw [hcomp, RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply,
          Algebra.TensorProduct.algebraMap_apply]
        congr 1
        rw [IsScalarTower.algebraMap_apply K Bm Aj] }
  trivial

end

end S1747Probe
