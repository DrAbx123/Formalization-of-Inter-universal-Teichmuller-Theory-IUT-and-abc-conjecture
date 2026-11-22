import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Algebra.RestrictScalars

noncomputable section
open scoped TensorProduct
namespace T1785b

variable {K Bm Ai : Type} [Field K] [Field Bm] [Field Ai]
  [Algebra K Bm] [Algebra K Ai]
  [Module.Finite K Ai] [Algebra.IsSeparable K Ai]

example (σ : Bm →ₐ[K] Ai) : True := by
  letI : Algebra Bm Ai := σ.toRingHom.toAlgebra
  haveI hTow : IsScalarTower K Bm Ai := IsScalarTower.of_algebraMap_eq (fun k => (σ.commutes k).symm)
  haveI hSM : SMulCommClass Bm K Ai := IsScalarTower.to_smulCommClass'
  have h1 : Algebra K (Ai ⊗[Bm] Ai) := inferInstance
  have h2 : Algebra Ai (Ai ⊗[Bm] Ai) := inferInstance
  letI hAlgT : Algebra K (Ai ⊗[Bm] Ai) := Algebra.TensorProduct.leftAlgebra
  letI hAlgAT : Algebra Ai (Ai ⊗[Bm] Ai) := Algebra.TensorProduct.leftAlgebra
  have h3 : Algebra K (Ai ⊗[Bm] Ai) := inferInstance
  have h4 : Algebra Ai (Ai ⊗[Bm] Ai) := inferInstance
  have h5 : IsScalarTower K Bm (Ai ⊗[Bm] Ai) := IsScalarTower.of_algebraMap_eq (fun k => by
    simp only [Algebra.TensorProduct.algebraMap_def, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply K Bm Ai])
  have h6 : IsScalarTower K Ai (Ai ⊗[Bm] Ai) := IsScalarTower.of_algebraMap_eq (fun k => by
    simp only [Algebra.TensorProduct.algebraMap_def, RingHom.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply])
  haveI hEtB : Algebra.Etale Bm Ai := by
    refine ⟨Algebra.FormallyEtale.of_isSeparable Bm Ai, ?_⟩
    exact (Algebra.FinitePresentation.of_finiteType (R := Bm)).mp inferInstance
  haveI hKEt : Algebra.Etale K Ai := by
    refine ⟨Algebra.FormallyEtale.of_isSeparable K Ai, ?_⟩
    exact (Algebra.FinitePresentation.of_finiteType (R := K)).mp inferInstance
  haveI hEtT : Algebra.Etale K (Ai ⊗[Bm] Ai) := by
    haveI : Algebra.Etale Ai (Ai ⊗[Bm] Ai) := Algebra.Etale.baseChange
    exact Algebra.Etale.comp K Ai (Ai ⊗[Bm] Ai)
  trivial

end T1785b
