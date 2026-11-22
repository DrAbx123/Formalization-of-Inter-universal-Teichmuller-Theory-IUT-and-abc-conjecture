import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Tactic

open scoped TensorProduct

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorEqualizerFixedPoints

noncomputable section

universe u

variable (R A G : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [MulSemiringAction G A] [SMulCommClass G R A]

/-- The action map A → (G → A), a ↦ (g ↦ g • a). -/
noncomputable def actionToFunctions : A →ₐ[R] (G → A) where
  toFun a g := g • a
  map_one' := by funext g; simp
  map_mul' a b := by funext g; simp
  map_zero' := by funext g; simp
  map_add' a b := by funext g; simp [add_smul]
  commutes' r := by funext g; simp [smul_comm]

/-- The constant map A → (G → A). -/
noncomputable def constToFunctions : A →ₐ[R] (G → A) where
  toFun a _ := a
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The fixed-point subalgebra is the equalizer of the action and constant maps. -/
theorem equalizer_eq_fixedPoints :
    AlgHom.equalizer (actionToFunctions R A G) (constToFunctions R A G) =
      FixedPoints.subalgebra R A G := by
  ext x
  simp only [AlgHom.equalizer, Set.mem_setOf_eq, FixedPoints.subalgebra]
  change (actionToFunctions R A G x = constToFunctions R A G x) ↔
    x ∈ FixedPoints.subsemiring A G
  simp [actionToFunctions, constToFunctions, FixedPoints.subsemiring, funext_iff]

variable (T : Type u) [CommRing T] [Algebra R T]

/-- Action of G on T ⊗[R] A by acting on the second factor. -/
noncomputable def tensorActionAlgEquiv (g : G) :
    T ⊗[R] A ≃ₐ[R] T ⊗[R] A :=
  Algebra.TensorProduct.congr (AlgEquiv.refl (R := R) : T ≃ₐ[R] T)
    (MulSemiringAction.toAlgEquiv R A g)

lemma tensorActionAlgEquiv_tmul (g : G) (t : T) (a : A) :
    tensorActionAlgEquiv R A G T g (t ⊗ₜ[R] a) = t ⊗ₜ[R] (g • a) := by
  simp [tensorActionAlgEquiv, Algebra.TensorProduct.congr]

noncomputable def tensorActionMonoidHom :
    G →* (T ⊗[R] A ≃+* T ⊗[R] A) where
  toFun g := (tensorActionAlgEquiv R A G T g).toRingEquiv
  map_one' := by
    ext x
    induction x with
    | zero => simp
    | tmul t a => simp [tensorActionAlgEquiv_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  map_mul' g h := by
    ext x
    induction x with
    | zero => simp
    | tmul t a => simp [tensorActionAlgEquiv_tmul, mul_smul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]

noncomputable instance tensorMulSemiringAction :
    MulSemiringAction G (T ⊗[R] A) :=
  MulSemiringAction.compHom (T ⊗[R] A) (tensorActionMonoidHom R A G T)

lemma tensor_smul_tmul (g : G) (t : T) (a : A) :
    (g • ((t ⊗ₜ[R] a) : T ⊗[R] A)) = t ⊗ₜ[R] (g • a) := by
  change tensorActionAlgEquiv R A G T g (t ⊗ₜ[R] a) = _
  exact tensorActionAlgEquiv_tmul R A G T g t a

lemma tensorActionAlgEquiv_eq_smul (g : G) (x : T ⊗[R] A) :
    tensorActionAlgEquiv R A G T g x = g • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t a => rw [tensorActionAlgEquiv_tmul, tensor_smul_tmul]
  | add x y hx hy => simp [map_add, hx, hy]



lemma tensor_smul_left_tmul (t t' : T) (a : A) :
    (t • ((t' ⊗ₜ[R] a) : T ⊗[R] A)) = (t * t') ⊗ₜ[R] a := by
  rw [Algebra.smul_def]
  rw [show (algebraMap T (T ⊗[R] A)) t =
    (Algebra.TensorProduct.includeLeft (R := R) (S := T) t) by rfl]
  rw [Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.tmul_mul_tmul]
  simp

/-- The G-action on T ⊗[R] A commutes with T-scalar multiplication. -/
noncomputable instance tensorSMulCommClass :
    SMulCommClass G T (T ⊗[R] A) where
  smul_comm g t x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul t' a =>
        calc
          g • (t • (t' ⊗ₜ[R] a)) = g • ((t * t') ⊗ₜ[R] a) := by
            rw [tensor_smul_left_tmul]
          _ = (t * t') ⊗ₜ[R] (g • a) := tensor_smul_tmul R A G T g (t * t') a
          _ = t • ((t' ⊗ₜ[R] (g • a)) : T ⊗[R] A) :=
            (tensor_smul_left_tmul (R := R) (A := A) (T := T) (t := t) (t' := t') (a := g • a)).symm
          _ = t • (g • ((t' ⊗ₜ[R] a) : T ⊗[R] A)) := by rw [tensor_smul_tmul]
    | add x y hx hy => simp [smul_add, hx, hy]

/-- The action by G on T ⊗[R] A as a T-algebra homomorphism into functions. -/
noncomputable def tensorActHom :
    T ⊗[R] A →ₐ[T] (G → T ⊗[R] A) where
  toFun x g := tensorActionAlgEquiv R A G T g x
  map_one' := by funext g; simp
  map_mul' x y := by funext g; simp
  map_zero' := by funext g; simp
  map_add' x y := by funext g; simp
  commutes' t := by
    funext g
    change tensorActionAlgEquiv R A G T g (algebraMap T (T ⊗[R] A) t) =
      algebraMap T (T ⊗[R] A) t
    simp [tensorActionAlgEquiv, Algebra.TensorProduct.congr]

/-- The constant T-algebra hom T ⊗[R] A → (G → T ⊗[R] A). -/
noncomputable def tensorConstHom :
    T ⊗[R] A →ₐ[T] (G → T ⊗[R] A) where
  toFun x _ := x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The fixed points of the tensor product are the equalizer of the tensor
action and constant maps, as T-subalgebras. -/
theorem tensorAlgHomEqualizer_eq_fixedPoints :
    AlgHom.equalizer (tensorActHom R A G T) (tensorConstHom R A G T) =
      FixedPoints.subalgebra T (T ⊗[R] A) G := by
  ext x
  simp only [AlgHom.equalizer, Set.mem_setOf_eq, FixedPoints.subalgebra]
  change (tensorActHom R A G T x = tensorConstHom R A G T x) ↔
    x ∈ FixedPoints.subsemiring (T ⊗[R] A) G
  simp [tensorActHom, tensorConstHom, FixedPoints.subsemiring, funext_iff,
    tensorActionAlgEquiv_eq_smul]


end

end LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorEqualizerFixedPoints
