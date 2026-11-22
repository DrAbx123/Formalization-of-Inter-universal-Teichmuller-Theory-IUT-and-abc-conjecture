import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Artinian.Module
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.TensorProduct.Maps

open CategoryTheory
open scoped TensorProduct

universe u

namespace S1747Probe

section
variable {K Bm Ai Aj : Type} [Field K] [Field Bm] [Field Ai] [Field Aj]
  [Algebra K Bm] [Algebra K Ai] [Algebra K Aj]
  [Algebra Bm Ai] [Algebra Bm Aj] [IsScalarTower K Bm Ai] [IsScalarTower K Bm Aj]

example : True := by
  letI : Algebra K (Ai ⊗[Bm] Aj) := Algebra.TensorProduct.leftAlgebra
  haveI tower : IsScalarTower K Bm (Ai ⊗[Bm] Aj) :=
    IsScalarTower.of_algebraMap_eq fun k => by
      rw [Algebra.TensorProduct.algebraMap_def, Algebra.TensorProduct.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply K Bm Ai]
      rfl
  let g : Ai →ₐ[K] (Ai ⊗[Bm] Aj) :=
    Algebra.TensorProduct.includeLeft (R := Bm) (S := K) (A := Ai) (B := Aj)
  let h : Aj →ₐ[K] (Ai ⊗[Bm] Aj) :=
    (Algebra.TensorProduct.includeRight (R := Bm) (A := Ai) (B := Aj)).restrictScalars K
  have key (b : Bm) : g (algebraMap Bm Ai b) = h (algebraMap Bm Aj b) := by
    show (algebraMap Bm Ai b) ⊗ₜ[Bm] (1 : Aj) = (1 : Ai) ⊗ₜ[Bm] (algebraMap Bm Aj b)
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul b
  trivial

end

end S1747Probe
