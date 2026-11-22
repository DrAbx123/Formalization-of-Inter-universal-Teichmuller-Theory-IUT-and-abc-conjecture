import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Artinian.Module
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

open CategoryTheory
open scoped TensorProduct

universe u

namespace S1747Probe

variable {K Bm Ai Aj : Type} [Field K] [Field Bm] [Field Ai] [Field Aj]
  [Algebra K Bm] [Algebra K Ai] [Algebra K Aj]
  (σi : Bm →ₐ[K] Ai) (σj : Bm →ₐ[K] Aj)

example : True := by
  letI : Algebra Bm Ai := σi.toRingHom.toAlgebra
  letI : Algebra Bm Aj := σj.toRingHom.toAlgebra
  have hAi : IsScalarTower K Bm Ai := .of_algebraMap_eq fun k => (σi.commutes k).symm
  have hAj : IsScalarTower K Bm Aj := .of_algebraMap_eq fun k => (σj.commutes k).symm
  haveI := hAi
  haveI := hAj
  haveI : CommRing (Ai ⊗[Bm] Aj) := inferInstance
  haveI : Algebra K (Ai ⊗[Bm] Aj) := inferInstance
  -- includeLeft over K
  haveI : SMulCommClass Bm K Ai := inferInstance
  let g : Ai →ₐ[K] (Ai ⊗[Bm] Aj) :=
    Algebra.TensorProduct.includeLeft (R := Bm) (S := K) (A := Ai) (B := Aj)
  letI : Algebra Aj (Ai ⊗[Bm] Aj) := Algebra.TensorProduct.rightAlgebra
  haveI : IsScalarTower K Aj (Ai ⊗[Bm] Aj) := inferInstance
  have key (b : Bm) : σi b ⊗ₜ[Bm] (1 : Aj) = (1 : Ai) ⊗ₜ[Bm] (σj b) := by
    have h := congr_fun (congr_arg DFunLike.coe
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := Bm) (A := Ai) (B := Aj))) b
    simpa [Algebra.TensorProduct.includeLeftRingHom_apply,
      Algebra.TensorProduct.includeRight_apply] using h
  trivial

end S1747Probe
