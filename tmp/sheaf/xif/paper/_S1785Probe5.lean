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
namespace T1785c

variable {K : Type} [Field K]
variable {I J : Type} [Finite I] [Finite J]
variable (Ai : I → Type) [∀ i, Field (Ai i)] [∀ i, Algebra K (Ai i)]
  [∀ i, Module.Finite K (Ai i)] [∀ i, Algebra.IsSeparable K (Ai i)]
variable (Bj : J → Type) [∀ j, Field (Bj j)] [∀ j, Algebra K (Bj j)]
variable (m : I → J)
variable (σ : ∀ i, Bj (m i) →ₐ[K] Ai i)

lemma test (i : I) : True := by
  letI : Algebra (Bj (m i)) (Ai i) := (σ i).toRingHom.toAlgebra
  haveI hTow : IsScalarTower K (Bj (m i)) (Ai i) :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := Bj (m i)) (A := Ai i)
      (fun k => ((σ i).commutes k).symm)
  haveI hFinB : Module.Finite (Bj (m i)) (Ai i) :=
    Module.Finite.of_restrictScalars_finite (R := K) (A := Bj (m i)) (M := Ai i)
  haveI hSepB : Algebra.IsSeparable (Bj (m i)) (Ai i) :=
    Algebra.isSeparable_tower_top_of_isSeparable (F := K) (L := Bj (m i)) (E := Ai i)
  haveI hCommT : CommRing (Ai i ⊗[Bj (m i)] Ai i) := inferInstance
  have c1 : Algebra K (Ai i ⊗[Bj (m i)] Ai i) := inferInstance
  letI hAlgT : Algebra K (Ai i ⊗[Bj (m i)] Ai i) := Algebra.TensorProduct.leftAlgebra
  letI hAlgAT : Algebra (Ai i) (Ai i ⊗[Bj (m i)] Ai i) := Algebra.TensorProduct.leftAlgebra
  have c2 : Algebra K (Ai i ⊗[Bj (m i)] Ai i) := inferInstance
  have c3 : Algebra (Ai i) (Ai i ⊗[Bj (m i)] Ai i) := inferInstance
  haveI hTowT : IsScalarTower K (Bj (m i)) (Ai i ⊗[Bj (m i)] Ai i) :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := Bj (m i))
      (A := Ai i ⊗[Bj (m i)] Ai i) (fun k => by
        simp only [Algebra.TensorProduct.algebraMap_def, RingHom.comp_apply,
          IsScalarTower.algebraMap_apply K (Bj (m i)) (Ai i)])
  have c4 : Algebra K (Ai i ⊗[Bj (m i)] Ai i) := inferInstance
  haveI hTowAT : IsScalarTower K (Ai i) (Ai i ⊗[Bj (m i)] Ai i) :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := Ai i)
      (A := Ai i ⊗[Bj (m i)] Ai i) (fun k => by
        simp only [Algebra.TensorProduct.algebraMap_def, RingHom.comp_apply,
          Algebra.algebraMap_self, RingHom.id_apply])
  have c5 : Algebra K (Ai i ⊗[Bj (m i)] Ai i) := inferInstance
  trivial

end T1785c
