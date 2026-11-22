import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section
open scoped TensorProduct
namespace T1785e

variable {K : Type} [Field K] {I J : Type} [Finite I] [Finite J]

lemma test (Ai : I → Type) [∀ i, Field (Ai i)] [∀ i, Algebra K (Ai i)]
    [∀ i, Module.Finite K (Ai i)] [∀ i, Algebra.IsSeparable K (Ai i)]
    (Bj : J → Type) [∀ j, Field (Bj j)] [∀ j, Algebra K (Bj j)]
    (m : I → J) (σ : ∀ i, Bj (m i) →ₐ[K] Ai i) (i : I) : True := by
  letI : Algebra (Bj (m i)) (Ai i) := (σ i).toRingHom.toAlgebra
  haveI hTow : IsScalarTower K (Bj (m i)) (Ai i) :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := Bj (m i)) (A := Ai i)
      (fun k => ((σ i).commutes k).symm)
  haveI hFinB : Module.Finite (Bj (m i)) (Ai i) :=
    Module.Finite.of_restrictScalars_finite (R := K) (A := Bj (m i)) (M := Ai i)
  haveI hSepB : Algebra.IsSeparable (Bj (m i)) (Ai i) :=
    Algebra.isSeparable_tower_top_of_isSeparable (F := K) (L := Bj (m i)) (E := Ai i)
  haveI hEtB : Algebra.Etale (Bj (m i)) (Ai i) := by
    refine ⟨Algebra.FormallyEtale.of_isSeparable (Bj (m i)) (Ai i), ?_⟩
    exact (Algebra.FinitePresentation.of_finiteType (R := Bj (m i))).mp inferInstance
  haveI hSM : SMulCommClass (Bj (m i)) K (Ai i) := IsScalarTower.to_smulCommClass'
  haveI hCommT : CommRing (Ai i ⊗[Bj (m i)] Ai i) := inferInstance
  have c1 : Algebra K (Ai i ⊗[Bj (m i)] Ai i) := inferInstance
  have c2 : Algebra (Ai i) (Ai i ⊗[Bj (m i)] Ai i) := inferInstance
  trivial

end T1785e
