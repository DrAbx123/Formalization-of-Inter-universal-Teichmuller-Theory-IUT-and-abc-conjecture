import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Algebra.TensorProduct

/-!
# Base change of algebra-hom equalizers

For a tower R → S → T → T' and f g : A →ₐ[R] B, this file builds the
base-change map on AlgHom.equalizer using TensorProduct.cancelBaseChange, and
proves its codRestrict membership by tensor induction.
-/

noncomputable section

open scoped TensorProduct
open Algebra.TensorProduct

namespace ABCBridge.EqualizerBaseChangeMembership

universe u

variable {R S T T' A B : Type u}
  [CommRing R] [CommRing S] [CommRing T] [CommRing T']
  [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R T] [Algebra R T']
  [Algebra S T] [Algebra S T'] [Algebra T T']
  [IsScalarTower R S T] [IsScalarTower R S T'] [IsScalarTower S T T']
  [IsScalarTower R T T']
  [Algebra R A] [Algebra R B]
  (f g : A →ₐ[R] B)
  [Module.Flat R T] [Module.Flat R T']

abbrev EqualizerT : Subalgebra S (T ⊗[R] A) :=
  AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id S T) f)
    (Algebra.TensorProduct.map (AlgHom.id S T) g)

abbrev EqualizerT' : Subalgebra S (T' ⊗[R] A) :=
  AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id S T') f)
    (Algebra.TensorProduct.map (AlgHom.id S T') g)

noncomputable def cancelBaseChangeB :
    T' ⊗[T] (T ⊗[R] B) →ₐ[T'] T' ⊗[R] B :=
  (Algebra.TensorProduct.cancelBaseChange (R := R) (S := T) (T := T')
    (A := T') (B := B)).toAlgHom

noncomputable def equalizerBaseChangeAux :
    T' ⊗[T] EqualizerT (f := f) (g := g) →ₐ[T'] T' ⊗[R] B :=
  (cancelBaseChangeB (f := f) (g := g)).comp
    (Algebra.TensorProduct.map (AlgHom.id T' T')
      (AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id S T) f)
        (Algebra.TensorProduct.map (AlgHom.id S T) g)).val)

theorem equalizerBaseChangeAux_mem
    (x : T' ⊗[T] EqualizerT (f := f) (g := g)) :
    equalizerBaseChangeAux (f := f) (g := g) x ∈ EqualizerT' (f := f) (g := g) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      rw [AlgHom.mem_equalizer]
      simp [equalizerBaseChangeAux]
  | add x y hx hy =>
      rw [AlgHom.mem_equalizer] at hx hy ⊢
      simp [equalizerBaseChangeAux, map_add, hx, hy]
  | tmul t' e =>
      rw [AlgHom.mem_equalizer]
      have he : Algebra.TensorProduct.map (AlgHom.id S T) f
            (e : T ⊗[R] A) =
          Algebra.TensorProduct.map (AlgHom.id S T) g
            (e : T ⊗[R] A) := e.property
      simpa [equalizerBaseChangeAux, cancelBaseChangeB,
        Algebra.TensorProduct.cancelBaseChange_tmul,
        Algebra.TensorProduct.map_tmul, Algebra.smul_def, mul_comm] using congrArg
        (fun z => Algebra.TensorProduct.map (AlgHom.id S T')
          (AlgHom.id S S) z) he

noncomputable def equalizerBaseChange :
    T' ⊗[T] EqualizerT (f := f) (g := g) →ₐ[T'] EqualizerT' (f := f) (g := g) :=
  (equalizerBaseChangeAux (f := f) (g := g)).codRestrict
    (EqualizerT' (f := f) (g := g))
    (equalizerBaseChangeAux_mem (f := f) (g := g))

@[simp]
theorem equalizerBaseChange_apply
    (x : T' ⊗[T] EqualizerT (f := f) (g := g)) :
    (equalizerBaseChange (f := f) (g := g) x : T' ⊗[R] A) =
      equalizerBaseChangeAux (f := f) (g := g) x :=
  rfl

/-- Coercion formula for a pure tensor in `tensorEqualizerEquiv`. -/
theorem tensorEqualizerEquiv_coe_tmul
    (t : T) (e : AlgHom.equalizer f g) :
    ((AlgHom.tensorEqualizerEquiv (S := S) (T := T) f g (t ⊗ₜ[R] e) :
        AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id S T) f)
          (Algebra.TensorProduct.map (AlgHom.id S T) g)) : T ⊗[R] A) =
      t ⊗ₜ[R] (e : A) := by
  simp [AlgHom.tensorEqualizerEquiv_apply, AlgHom.coe_tensorEqualizer]

/-- Coercion formula for the base-change map on pure tensors. -/
theorem equalizerBaseChange_coe_tmul
    (t' : T') (e : EqualizerT (f := f) (g := g)) :
    (equalizerBaseChange (f := f) (g := g) (t' ⊗ₜ[T] e) : T' ⊗[R] A) =
      t' ⊗ₜ[R] (e : T ⊗[R] A) := by
  simp [equalizerBaseChange, equalizerBaseChangeAux, cancelBaseChangeB,
    Algebra.TensorProduct.cancelBaseChange_tmul]

/-- Naturality of `tensorEqualizerEquiv` under the tower `T → T'`. -/
theorem tensorEqualizerEquiv_naturality
    (x : T' ⊗[T] (T ⊗[R] AlgHom.equalizer f g)) :
    AlgHom.tensorEqualizerEquiv (S := S) (T := T') f g
        (Algebra.TensorProduct.cancelBaseChange (R := R) (S := T) (T := T')
          (A := T') (B := AlgHom.equalizer f g) x) =
      equalizerBaseChange (f := f) (g := g)
        (Algebra.TensorProduct.map (AlgHom.id T' T')
          (AlgHom.tensorEqualizerEquiv (S := S) (T := T) f g) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul t' e =>
      induction e using TensorProduct.induction_on with
      | zero => simp
      | add e₁ e₂ h₁ h₂ => simp [map_add, h₁, h₂]
      | tmul t a =>
          simp [Algebra.TensorProduct.cancelBaseChange_tmul,
            tensorEqualizerEquiv_coe_tmul, equalizerBaseChange_coe_tmul,
            Algebra.TensorProduct.map_tmul, Algebra.smul_def, mul_comm]

end ABCBridge.EqualizerBaseChangeMembership
