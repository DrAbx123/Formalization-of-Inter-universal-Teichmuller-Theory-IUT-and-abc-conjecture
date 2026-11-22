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

-- set the K-algebra structure on the tensor to the left one
example : True := by
  letI : Algebra K (Ai ⊗[Bm] Aj) := Algebra.TensorProduct.leftAlgebra
  let g : Ai →ₐ[K] (Ai ⊗[Bm] Aj) :=
    Algebra.TensorProduct.includeLeft (R := Bm) (S := K) (A := Ai) (B := Aj)
  -- now the right factor
  letI : Algebra Aj (Ai ⊗[Bm] Aj) := Algebra.TensorProduct.rightAlgebra
  haveI : IsScalarTower K Aj (Ai ⊗[Bm] Aj) := IsScalarTower.of_algebraMap_eq fun k => by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.algebraMap_apply, IsScalarTower.algebraMap_apply Bm Aj (Ai ⊗[Bm] Aj)]
    -- goal about tensor elements
    sorry
  trivial

end

end S1747Probe
