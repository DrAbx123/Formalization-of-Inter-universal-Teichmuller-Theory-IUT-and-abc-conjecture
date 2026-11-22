import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.Algebra.Algebra.RestrictScalars

noncomputable section
open scoped TensorProduct

namespace S1785Probe

variable {K Bm Ai : Type} [Field K] [Field Bm] [Field Ai]
  [Algebra K Bm] [Algebra K Ai] [Algebra Bm Ai] [IsScalarTower K Bm Ai]
  [Module.Finite K Ai]

lemma nat_eq_one_of_mul_self_eq_self {d : ℕ} (h : d * d = d) (hpos : 0 < d) : d = 1 := by
  have h1 : d * (d - 1) = 0 := by
    rw [Nat.mul_sub_one, h, Nat.sub_self]
  rcases Nat.mul_eq_zero.mp h1 with h2 | h2
  · omega
  · omega

set_option maxHeartbeats 800000 in
lemma surjective_algebraMap_of_tmul_comm
    [Algebra.IsSeparable K Ai]
    (hcomm : ∀ x : Ai, x ⊗ₜ[Bm] (1 : Ai) = (1 : Ai) ⊗ₜ[Bm] x) :
    Function.Surjective (algebraMap Bm Ai) := by
  haveI : Module.Finite Bm Ai :=
    Module.Finite.of_restrictScalars_finite (R := K) (A := Bm) (M := Ai)
  have hsurj : Function.Surjective (Algebra.TensorProduct.lmul' (R := Bm) : Ai ⊗[Bm] Ai →ₐ[Bm] Ai) := by
    intro x
    exact ⟨x ⊗ₜ[Bm] 1, by simp⟩
  have key : ∀ z : Ai ⊗[Bm] Ai,
      Algebra.TensorProduct.includeLeft (R := Bm) (S := Bm) (A := Ai) (B := Ai)
        (Algebra.TensorProduct.lmul' (R := Bm) z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
        rw [Algebra.TensorProduct.lmul'_apply_tmul, map_mul]
        calc Algebra.TensorProduct.includeLeft (R := Bm) (S := Bm) (A := Ai) (B := Ai) x *
              Algebra.TensorProduct.includeLeft (R := Bm) (S := Bm) (A := Ai) (B := Ai) y
            = (x ⊗ₜ[Bm] 1) * (y ⊗ₜ[Bm] 1) := by rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeLeft_apply]
          _ = (x ⊗ₜ[Bm] 1) * (1 ⊗ₜ[Bm] y) := by rw [hcomm y]
          _ = x ⊗ₜ[Bm] y := by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hinj : Function.Injective (Algebra.TensorProduct.lmul' (R := Bm) : Ai ⊗[Bm] Ai →ₐ[Bm] Ai) := by
    intro x y hxy
    have h1 := key x
    have h2 := key y
    rw [hxy] at h1
    rw [h2] at h1
    exact h1.symm
  have hbij : Function.Bijective (Algebra.TensorProduct.lmul' (R := Bm) : Ai ⊗[Bm] Ai →ₐ[Bm] Ai) := ⟨hinj, hsurj⟩
  let e : (Ai ⊗[Bm] Ai) ≃ₗ[Bm] Ai :=
    LinearEquiv.ofBijective (Algebra.TensorProduct.lmul' (R := Bm)).toLinearMap hbij
  have h1 : Module.finrank Bm (Ai ⊗[Bm] Ai) = Module.finrank Bm Ai := e.finrank_eq
  have h2 : Module.finrank Bm (Ai ⊗[Bm] Ai) = Module.finrank Bm Ai * Module.finrank Bm Ai :=
    Module.finrank_tensorProduct (R := Bm) (S := Bm) (M := Ai) (M' := Ai)
  have hdd : Module.finrank Bm Ai * Module.finrank Bm Ai = Module.finrank Bm Ai := by rw [← h2, h1]
  have hpos : 0 < Module.finrank Bm Ai := by
    rw [Module.finrank_pos_iff_of_free Bm Ai]
    infer_instance
  have hone : Module.finrank Bm Ai = 1 := nat_eq_one_of_mul_self_eq_self hdd hpos
  exact ((Algebra.finrank_eq_one_iff_bijective_algebraMap (F := Bm) (E := Ai)).mp hone).2

end S1785Probe
