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

example : SMulCommClass Bm K Ai := by infer_instance
example : SMulCommClass Bm K Aj := by infer_instance

example : Algebra K (Ai ⊗[Bm] Aj) := Algebra.TensorProduct.leftAlgebra
example : Algebra Ai (Ai ⊗[Bm] Aj) := inferInstance

end

end S1747Probe
