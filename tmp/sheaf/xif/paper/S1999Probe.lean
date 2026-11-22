import tmp.sheaf.xif.paper.S1993D5FiniteGroupBridgeActual
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Algebra.Algebra.Bilinear

noncomputable section
set_option maxHeartbeats 800000
open Polynomial

example : (X ^ 2 + C (1 : ℚ)).natDegree = 2 := by
  rw [natDegree_X_pow_add_C]

example {E : Type*} [Field E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    (hodd : Odd (Module.finrank ℚ E)) (y : E) (hy : y ^ 2 = -1) : False := by
  let T : Module.End ℚ E := Algebra.lmul ℚ y
  have happ : ∀ z : E, T z = y * z := fun z => by
    simp [T]
  have hT : T * T = -1 := by
    ext z
    rw [Module.End.mul_apply, happ, happ, ← mul_assoc, hy]
    simp
  have hdet : LinearMap.det T * LinearMap.det T = -1 := by
    have h := congrArg (LinearMap.det : Module.End ℚ E → ℚ) hT
    rw [map_mul] at h
    have hone : LinearMap.det (-1 : Module.End ℚ E) = -1 := by
      have h1 : (-1 : Module.End ℚ E) = (-1 : ℚ) • (1 : Module.End ℚ E) := by
        rw [neg_one_smul]
      rw [h1, LinearMap.det_smul, map_one, one_mul, hodd.neg_one_pow]
    rwa [hone] at h
  nlinarith [sq_nonneg (LinearMap.det T)]

open LeanFormal.IUT.XiFPaper.S1993D5FiniteGroupBridgeActual in
example (x : S1993KP) : x ∈ (ℚ⟮S1993SqrtNegThree⟯ ⊔ ℚ⟮x⟯ : IntermediateField ℚ S1993KP) :=
  le_sup_right (IntermediateField.mem_adjoin_simple_self ℚ x)
