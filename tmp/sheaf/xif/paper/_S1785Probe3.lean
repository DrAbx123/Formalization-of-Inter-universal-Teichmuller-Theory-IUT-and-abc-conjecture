import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Algebra.RestrictScalars

noncomputable section
open scoped TensorProduct
namespace T1785

variable {K Bm Ai : Type} [Field K] [Field Bm] [Field Ai]
  [Algebra K Bm] [Algebra K Ai] [Algebra Bm Ai] [IsScalarTower K Bm Ai]

example : SMulCommClass Bm K Ai := inferInstance
example : Algebra K (Ai ⊗[Bm] Ai) := inferInstance
example : Algebra Ai (Ai ⊗[Bm] Ai) := inferInstance

example : True := by
  haveI hSM : SMulCommClass Bm K Ai := inferInstance
  letI hAlgT : Algebra K (Ai ⊗[Bm] Ai) := Algebra.TensorProduct.leftAlgebra
  letI hAlgAT : Algebra Ai (Ai ⊗[Bm] Ai) := Algebra.TensorProduct.leftAlgebra
  have h1 : Algebra K (Ai ⊗[Bm] Ai) := inferInstance
  have h2 : Algebra Ai (Ai ⊗[Bm] Ai) := inferInstance
  have h3 : IsScalarTower K Bm (Ai ⊗[Bm] Ai) := IsScalarTower.of_algebraMap_eq (fun k => by
    simp only [Algebra.TensorProduct.algebraMap_def, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply K Bm Ai])
  have h4 : IsScalarTower K Ai (Ai ⊗[Bm] Ai) := IsScalarTower.of_algebraMap_eq (fun k => by
    simp only [Algebra.TensorProduct.algebraMap_def, RingHom.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply])
  trivial

end T1785
