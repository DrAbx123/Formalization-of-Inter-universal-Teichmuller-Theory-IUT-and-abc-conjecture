import LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorEqualizerFixedPoints
import Mathlib.RingTheory.TensorProduct.Pi

set_option maxHeartbeats 3000000
open scoped TensorProduct

namespace M1Final
open LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorEqualizerFixedPoints

universe u
variable {R A G : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G] [MulSemiringAction G A] [SMulCommClass G R A]
variable {T : Type u} [CommRing T] [Algebra R T] [Module.Flat R T]

noncomputable def piEquiv :
    T ⊗[R] (G → A) ≃ₐ[T] (G → T ⊗[R] A) :=
  Algebra.TensorProduct.piRight (R := R) (S := T) (A := T) (B := fun _ : G => A)

lemma piEquiv_map_action (x : T ⊗[R] A) :
    piEquiv (R := R) (A := A) (G := G) (T := T)
        (Algebra.TensorProduct.map (AlgHom.id T T) (actionToFunctions R A G) x) =
      tensorActHom R A G T x := by
  ext g
  induction x using TensorProduct.induction_on with
  | zero => simp [piEquiv, tensorActHom]
  | tmul t a =>
      simp [piEquiv, tensorActHom, tensorActionAlgEquiv, actionToFunctions]
  | add x y hx hy => simp [map_add, hx, hy]

lemma piEquiv_map_const (x : T ⊗[R] A) :
    piEquiv (R := R) (A := A) (G := G) (T := T)
        (Algebra.TensorProduct.map (AlgHom.id T T) (constToFunctions R A G) x) =
      tensorConstHom R A G T x := by
  ext g
  induction x using TensorProduct.induction_on with
  | zero => simp [piEquiv, tensorConstHom]
  | tmul t a => simp [piEquiv, tensorConstHom, constToFunctions]
  | add x y hx hy => simp [map_add, hx, hy]

lemma tensorTargetEqualizer_eq_fixedPoints :
    AlgHom.equalizer
        (Algebra.TensorProduct.map (AlgHom.id T T) (actionToFunctions R A G))
        (Algebra.TensorProduct.map (AlgHom.id T T) (constToFunctions R A G)) =
      FixedPoints.subalgebra T (T ⊗[R] A) G := by
  rw [← tensorAlgHomEqualizer_eq_fixedPoints R A G T]
  ext x
  rw [AlgHom.mem_equalizer, AlgHom.mem_equalizer]
  constructor
  · intro h
    have h' := congrArg (piEquiv (R := R) (A := A) (G := G) (T := T)) h
    simpa [piEquiv_map_action, piEquiv_map_const] using h'
  · intro h
    apply (piEquiv (R := R) (A := A) (G := G) (T := T)).injective
    simpa [piEquiv_map_action, piEquiv_map_const] using h

noncomputable def tensorFixedPointsAlgEquiv :
    T ⊗[R] FixedPoints.subalgebra R A G ≃ₐ[T]
      FixedPoints.subalgebra T (T ⊗[R] A) G :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[T] T)
    (Subalgebra.equivOfEq _ _ (equalizer_eq_fixedPoints R A G))).symm.trans
  ((AlgHom.tensorEqualizerEquiv (S := T) (T := T)
      (actionToFunctions R A G) (constToFunctions R A G)).trans
    (Subalgebra.equivOfEq _ _ (tensorTargetEqualizer_eq_fixedPoints (R := R) (A := A) (G := G) (T := T))))

end M1Final
