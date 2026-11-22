import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.TensorProduct.Finite

noncomputable section
open CategoryTheory
open scoped TensorProduct
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2526FiniteEtaleClosureActual

universe u

variable (R : Type u) [CommRing R]

theorem S2526_tensor_etale (A B : Type u) [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [Algebra.Etale R A] [Algebra.Etale R B] :
    Algebra.Etale R (A ⊗[R] B) := by
  letI : Algebra A (A ⊗[R] B) :=
    Algebra.TensorProduct.leftAlgebra (R := R) (S := A) (A := A) (B := B)
  haveI : IsScalarTower R A (A ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      rw [Algebra.TensorProduct.algebraMap_apply (S := A),
        Algebra.TensorProduct.algebraMap_apply']
      simpa [Algebra.algebraMap_eq_smul_one] using
        (TensorProduct.smul_tmul (R := R) (R' := R) r (1 : A) (1 : B)).symm)
  exact Algebra.Etale.comp R A (A ⊗[R] B)

theorem S2526_tensor_finite (A B : Type u) [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Finite R A] [Module.Finite R B] :
    Module.Finite R (A ⊗[R] B) := by infer_instance

noncomputable def S2526TensorObj (A B : CommAlgCat.FiniteEtale R) :
    CommAlgCat.FiniteEtale R := by
  haveI := S2526_tensor_etale R A.obj B.obj
  exact CommAlgCat.FiniteEtale.of (R := R) (S := A.obj ⊗[R] B.obj)

#check S2526TensorObj
end LeanFormal.IUT.XiFPaper.S2526FiniteEtaleClosureActual
end