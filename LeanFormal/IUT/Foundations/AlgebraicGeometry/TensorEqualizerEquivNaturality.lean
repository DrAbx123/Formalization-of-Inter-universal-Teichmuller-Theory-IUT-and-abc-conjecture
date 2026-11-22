import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.TensorProduct.Maps
import LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorFixedPointsBaseChange
import LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorEqualizerFixedPoints
import Mathlib.LinearAlgebra.TensorProduct.Tower

noncomputable section
open scoped TensorProduct
open Algebra.TensorProduct

namespace ABCBridge.TensorEqualizerEquivNaturality
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

abbrev EqualizerT : Subalgebra T (T ⊗[R] A) :=
  AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id T T) f)
    (Algebra.TensorProduct.map (AlgHom.id T T) g)

abbrev EqualizerT' : Subalgebra T' (T' ⊗[R] A) :=
  AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id T' T') f)
    (Algebra.TensorProduct.map (AlgHom.id T' T') g)

noncomputable def cancelA :
    T' ⊗[T] (T ⊗[R] A) →ₐ[T'] T' ⊗[R] A :=
  (Algebra.TensorProduct.cancelBaseChange (R := R) (S := T) (T := T')
    (A := T') (B := A)).toAlgHom

noncomputable def equalizerBaseChangeAux :
    T' ⊗[T] EqualizerT (T := T) (f := f) (g := g) →ₐ[T'] T' ⊗[R] A :=
  (cancelA (R := R) (T := T) (T' := T') (A := A)).comp
    (Algebra.TensorProduct.map (AlgHom.id T' T') (EqualizerT (T := T) (f := f) (g := g)).val)

/-- Pure-tensor formula for the cancellation map. -/
theorem cancelA_tmul (t' : T') (z : T ⊗[R] A) :
    cancelA (R := R) (T := T) (T' := T') (A := A) (t' ⊗ₜ[T] z) =
      t' • Algebra.TensorProduct.map (IsScalarTower.toAlgHom R T T')
        (AlgHom.id R A) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp [cancelA]
  | add z1 z2 h1 h2 =>
      rw [TensorProduct.tmul_add, map_add]
      simp [map_add, smul_add, h1, h2]
  | tmul t0 a =>
      simp [cancelA, Algebra.TensorProduct.cancelBaseChange_tmul,
        Algebra.TensorProduct.map_tmul, Algebra.smul_def, mul_comm]

theorem map_cancelA (t' : T') (z : T ⊗[R] A) :
    (Algebra.TensorProduct.map (AlgHom.id T' T') f) (cancelA (R := R) (T := T)
      (T' := T') (A := A) (t' ⊗ₜ[T] z)) =
      t' • Algebra.TensorProduct.map (IsScalarTower.toAlgHom R T T') f z := by
  induction z using TensorProduct.induction_on with
  | zero => simp [cancelA]
  | add z1 z2 h1 h2 =>
      rw [TensorProduct.tmul_add, map_add, map_add]
      simp [map_add, smul_add, h1, h2]
  | tmul t0 a =>
      simp [cancelA, Algebra.TensorProduct.cancelBaseChange_tmul,
        Algebra.TensorProduct.map_tmul, Algebra.smul_def, mul_comm, mul_left_comm,
        mul_assoc]

theorem equalizerBaseChangeAux_mem
    (x : T' ⊗[T] EqualizerT (T := T) (f := f) (g := g)) :
    equalizerBaseChangeAux (f := f) (g := g) x ∈ EqualizerT' (T' := T') (f := f) (g := g) := by
  induction x using TensorProduct.induction_on with
  | zero => simp [equalizerBaseChangeAux]
  | add x y hx hy =>
      rw [map_add]
      exact (EqualizerT' (T' := T') (f := f) (g := g)).add_mem hx hy
  | tmul t' e =>
      rw [AlgHom.mem_equalizer]
      simp only [equalizerBaseChangeAux, AlgHom.comp_apply, AlgHom.id_apply, Algebra.TensorProduct.map_tmul]
      have he : Algebra.TensorProduct.map (AlgHom.id T T) f (e : T ⊗[R] A) =
          Algebra.TensorProduct.map (AlgHom.id T T) g (e : T ⊗[R] A) := e.property
      have hpoint_f : ∀ z : T ⊗[R] A,
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R T T')
            (AlgHom.id R B)) ((Algebra.TensorProduct.map (AlgHom.id T T) f) z) =
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R T T') f) z := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | add z1 z2 h1 h2 => simp [map_add, h1, h2]
        | tmul t0 a => simp [Algebra.TensorProduct.map_tmul]
      have hpoint_g : ∀ z : T ⊗[R] A,
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R T T')
            (AlgHom.id R B)) ((Algebra.TensorProduct.map (AlgHom.id T T) g) z) =
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R T T') g) z := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | add z1 z2 h1 h2 => simp [map_add, h1, h2]
        | tmul t0 a => simp [Algebra.TensorProduct.map_tmul]
      have hmap := congrArg
        (fun z : T ⊗[R] B => t' • Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom R T T') (AlgHom.id R B) z) he
      rw [map_cancelA (f := f) t' ((EqualizerT (T := T) f g).val e),
        map_cancelA (f := g) t' ((EqualizerT (T := T) f g).val e)]
      simpa [hpoint_f, hpoint_g] using hmap

noncomputable def equalizerBaseChange :
    T' ⊗[T] EqualizerT (T := T) (f := f) (g := g) →ₐ[T'] EqualizerT' (T' := T') (f := f) (g := g) :=
  (equalizerBaseChangeAux (f := f) (g := g)).codRestrict
    (EqualizerT' (T' := T') (f := f) (g := g))
    (equalizerBaseChangeAux_mem (f := f) (g := g))

@[simp] theorem equalizerBaseChange_apply
    (x : T' ⊗[T] EqualizerT (T := T) (f := f) (g := g)) :
    (equalizerBaseChange (f := f) (g := g) x : T' ⊗[R] A) =
      equalizerBaseChangeAux (f := f) (g := g) x := rfl

theorem tensorEqualizerEquiv_coe_tmul
    (t : T) (e : AlgHom.equalizer f g) :
    ((AlgHom.tensorEqualizerEquiv (S := T) (T := T) f g (t ⊗ₜ[R] e) :
        EqualizerT (T := T) (f := f) (g := g)) : T ⊗[R] A) =
      t ⊗ₜ[R] (e : A) := by
  simp [AlgHom.tensorEqualizerEquiv_apply, AlgHom.coe_tensorEqualizer,
    Algebra.TensorProduct.map_tmul, Algebra.smul_def]

theorem equalizerBaseChange_coe_tmul
    (t' : T') (e : EqualizerT (T := T) (f := f) (g := g)) :
    (equalizerBaseChange (f := f) (g := g) (t' ⊗ₜ[T] e) : T' ⊗[R] A) =
      t' • Algebra.TensorProduct.map (IsScalarTower.toAlgHom R T T')
        (AlgHom.id R A) (e : T ⊗[R] A) := by
  simpa [equalizerBaseChange, equalizerBaseChangeAux] using
    cancelA_tmul (R := R) (T := T) (T' := T') (A := A) t' (e : T ⊗[R] A)

theorem tensorEqualizerEquiv_naturality
    (x : T' ⊗[T] (T ⊗[R] AlgHom.equalizer f g)) :
    AlgHom.tensorEqualizerEquiv (S := T') (T := T') f g
        (Algebra.TensorProduct.cancelBaseChange (R := R) (S := T) (T := T')
          (A := T') (B := AlgHom.equalizer f g) x) =
      equalizerBaseChange (f := f) (g := g)
        (Algebra.TensorProduct.map (AlgHom.id T' T')
          (AlgHom.tensorEqualizerEquiv (S := T) (T := T) f g) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul t' e =>
      induction e using TensorProduct.induction_on with
      | zero => simp
      | add e1 e2 h1 h2 =>
          simp [TensorProduct.tmul_add, map_add, h1, h2]
      | tmul t a =>
          apply Subtype.ext
          simp [Algebra.TensorProduct.cancelBaseChange_tmul,
            AlgHom.coe_tensorEqualizer, tensorEqualizerEquiv_coe_tmul,
            equalizerBaseChange_apply, equalizerBaseChangeAux, cancelA_tmul, Algebra.TensorProduct.map_tmul,
            Algebra.smul_def, mul_comm, mul_assoc]

section FixedPointsLocalization

open M1Final
open LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorEqualizerFixedPoints

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
  [MulSemiringAction G A] [SMulCommClass G R A]

/-- Base change of the fixed-point subalgebra along T -> T'. -/
noncomputable def fixedPointBaseChange :
    T' ⊗[T] FixedPoints.subalgebra T (T ⊗[R] A) G →ₐ[T']
      FixedPoints.subalgebra T' (T' ⊗[R] A) G :=
  (M1Final.tensorFixedPointsAlgEquiv (R := R) (A := A) (G := G) (T := T')).toAlgHom.comp
    ((Algebra.TensorProduct.cancelBaseChange (R := R) (S := T) (T := T')
        (A := T') (B := FixedPoints.subalgebra R A G)).toAlgHom.comp
      (Algebra.TensorProduct.congr (AlgEquiv.refl : T' ≃ₐ[T'] T')
        (M1Final.tensorFixedPointsAlgEquiv (R := R) (A := A) (G := G) (T := T)).symm).toAlgHom)

/-- M1 naturality under the tower T -> T': the localized fixed-point
equivalence commutes with base change. -/
theorem tensorFixedPointsAlgEquiv_naturality
    (x : T' ⊗[T] (T ⊗[R] FixedPoints.subalgebra R A G)) :
    tensorFixedPointsAlgEquiv (R := R) (A := A) (G := G) (T := T')
        (Algebra.TensorProduct.cancelBaseChange (R := R) (S := T) (T := T')
          (A := T') (B := FixedPoints.subalgebra R A G) x) =
      fixedPointBaseChange
        (Algebra.TensorProduct.map (AlgHom.id T' T')
          (tensorFixedPointsAlgEquiv (R := R) (A := A) (G := G) (T := T)).toAlgHom x) := by
  simp [fixedPointBaseChange, Algebra.TensorProduct.congr_apply]
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
  simp

end FixedPointsLocalization

end ABCBridge.TensorEqualizerEquivNaturality
