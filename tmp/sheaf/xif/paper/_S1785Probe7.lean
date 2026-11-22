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
namespace T1785f

variable {K : Type} [Field K] {I J : Type} [Finite I] [Finite J]

lemma test (Ai : I → Type) [∀ i, Field (Ai i)] [∀ i, Algebra K (Ai i)]
    [∀ i, Module.Finite K (Ai i)] [∀ i, Algebra.IsSeparable K (Ai i)]
    (Bj : J → Type) [∀ j, Field (Bj j)] [∀ j, Algebra K (Bj j)]
    [∀ j, Module.Finite K (Bj j)]
    (m : I → J) (σ : ∀ i, Bj (m i) →ₐ[K] Ai i)
    (psi : (∀ j, Bj j) →ₐ[K] (∀ i, Ai i))
    (hpsi : ∀ (i : I) (x : ∀ j, Bj j), psi x i = σ i (x (m i)))
    (i : I) : True := by
  classical
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
  set_option trace.Meta.synthInstance true in
  have c1 : Algebra K (Ai i ⊗[Bj (m i)] Ai i) := inferInstance
  have c2 : Algebra (Ai i) (Ai i ⊗[Bj (m i)] Ai i) := inferInstance
  have c3 : Module.Finite K (Ai i ⊗[Bj (m i)] Ai i) := by
    haveI : Module.Finite (Bj (m i)) (Ai i ⊗[Bj (m i)] Ai i) :=
      Module.Finite.tensorProduct (Bj (m i)) (Ai i) (Ai i)
    exact Module.Finite.trans (R := K) (Bj (m i)) (Ai i ⊗[Bj (m i)] Ai i)
  have c4 : Algebra.Etale K (Ai i ⊗[Bj (m i)] Ai i) := by
    haveI : Algebra.Etale (Ai i) (Ai i ⊗[Bj (m i)] Ai i) := Algebra.Etale.baseChange
    exact Algebra.Etale.comp K (Ai i) (Ai i ⊗[Bj (m i)] Ai i)
  trivial

end T1785f