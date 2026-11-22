/-
S1847 probe 1: fixed points commute with base change (tame / Reynolds case).
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleFixedPoints
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Map

noncomputable section
open scoped TensorProduct

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace S1847Probe1

section Main

variable {R T A G : Type}
  [CommRing R] [CommRing T] [Algebra R T]
  [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G R A]

variable [MulSemiringAction G (T ⊗[R] A)] [SMulCommClass G T (T ⊗[R] A)]

/-- The fixed point subalgebra, in the form used by the Reynolds operator. -/
abbrev FPS : Subalgebra R A := ABCBridge.FiniteEtaleFixedPoints.fixedPointSubalgebra R A G

/-- The canonical T-algebra map from T tensor A^G to T tensor A. -/
noncomputable def phiHom :
    T ⊗[R] ↥(FPS (R := R) (A := A) (G := G)) →ₐ[T] T ⊗[R] A :=
  Algebra.TensorProduct.map (AlgHom.id T T) (FPS (R := R) (A := A) (G := G)).val

lemma phiHom_tmul (t : T) (b : ↥(FPS (R := R) (A := A) (G := G))) :
    phiHom (R := R) (T := T) (A := A) (G := G) (t ⊗ₜ[R] b) = t ⊗ₜ[R] (b : A) := by
  rw [phiHom, Algebra.TensorProduct.map_tmul]
  simp

/-- The same map as a linear map. -/
noncomputable def inkl :
    T ⊗[R] ↥(FPS (R := R) (A := A) (G := G)) →ₗ[R] T ⊗[R] A :=
  (phiHom (R := R) (T := T) (A := A) (G := G)).toLinearMap

lemma inkl_tmul (t : T) (b : ↥(FPS (R := R) (A := A) (G := G))) :
    inkl (R := R) (T := T) (A := A) (G := G) (t ⊗ₜ[R] b) = t ⊗ₜ[R] (b : A) :=
  phiHom_tmul t b

/-- The Reynolds projection from T tensor A to T tensor A^G. -/
noncomputable def prj (hG : IsUnit (Fintype.card G : R)) :
    T ⊗[R] A →ₗ[R] T ⊗[R] ↥(FPS (R := R) (A := A) (G := G)) :=
  (ABCBridge.FiniteEtaleFixedPoints.reynolds R A G hG).lTensor T

lemma prj_tmul (hG : IsUnit (Fintype.card G : R)) (t : T) (a : A) :
    prj (R := R) (A := A) (G := G) hG (t ⊗ₜ[R] a) =
      t ⊗ₜ[R] (ABCBridge.FiniteEtaleFixedPoints.reynolds R A G hG a) := by
  rw [prj, LinearMap.lTensor_tmul]

/-- Key identity: the composite T tensor A -> T tensor A^G -> T tensor A is the
orbit sum, rescaled by the inverse of the group order. -/
lemma inkl_prj (hact : ∀ (g : G) (t : T) (a : A), g • (t ⊗ₜ[R] a) = t ⊗ₜ[R] (g • a))
    (hG : IsUnit (Fintype.card G : R)) (x : T ⊗[R] A) :
    inkl (R := R) (T := T) (A := A) (G := G) (prj (R := R) (A := A) (G := G) hG x) =
      ABCBridge.FiniteEtaleFixedPoints.groupCardInv R G hG • (∑ g : G, g • x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t a =>
      rw [prj_tmul, inkl_tmul,
        ABCBridge.FiniteEtaleFixedPoints.reynolds_apply_coe,
        TensorProduct.tmul_smul]
      congr 1
      rw [ABCBridge.FiniteEtaleFixedPoints.orbitSum_apply, TensorProduct.tmul_sum]
      exact Finset.sum_congr rfl (fun g _ => (hact g t a).symm)
  | add x y hx hy =>
      have hsum : (∑ g : G, g • (x + y)) = (∑ g : G, g • x) + (∑ g : G, g • y) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun g _ => smul_add g x y)
      rw [hsum, smul_add]
      simp only [map_add, hx, hy]

/-- The Reynolds projection retracts the inclusion. -/
lemma prj_inkl (hG : IsUnit (Fintype.card G : R))
    (y : T ⊗[R] ↥(FPS (R := R) (A := A) (G := G))) :
    prj (R := R) (A := A) (G := G) hG (inkl (R := R) (T := T) (A := A) (G := G) y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul t b =>
      rw [inkl_tmul, prj_tmul]
      congr 1
      have h := congrArg (fun f => f b)
        (ABCBridge.FiniteEtaleFixedPoints.reynolds_comp_inclusion R A G hG)
      simpa using h
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The canonical map lands in the fixed points of the base change. -/
lemma phiHom_mem (hact : ∀ (g : G) (t : T) (a : A), g • (t ⊗ₜ[R] a) = t ⊗ₜ[R] (g • a))
    (x : T ⊗[R] ↥(FPS (R := R) (A := A) (G := G))) :
    phiHom (R := R) (T := T) (A := A) (G := G) x ∈ FPS (R := T) (A := T ⊗[R] A) (G := G) := by
  intro g
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t b =>
      rw [phiHom_tmul, hact]
      rw [b.2 g]
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

/-- The canonical map as a T-algebra map into the fixed points. -/
noncomputable def phiSub (hact : ∀ (g : G) (t : T) (a : A), g • (t ⊗ₜ[R] a) = t ⊗ₜ[R] (g • a)) :
    T ⊗[R] ↥(FPS (R := R) (A := A) (G := G)) →ₐ[T]
      ↥(FPS (R := T) (A := T ⊗[R] A) (G := G)) :=
  (phiHom (R := R) (T := T) (A := A) (G := G)).codRestrict _ (phiHom_mem hact)

lemma phiSub_coe (hact : ∀ (g : G) (t : T) (a : A), g • (t ⊗ₜ[R] a) = t ⊗ₜ[R] (g • a))
    (x : T ⊗[R] ↥(FPS (R := R) (A := A) (G := G))) :
    ((phiSub (R := R) (T := T) (A := A) (G := G) hact x : ↥(FPS (R := T) (A := T ⊗[R] A) (G := G))) :
      T ⊗[R] A) = inkl (R := R) (T := T) (A := A) (G := G) x := rfl

lemma phiSub_injective (hact : ∀ (g : G) (t : T) (a : A), g • (t ⊗ₜ[R] a) = t ⊗ₜ[R] (g • a))
    (hG : IsUnit (Fintype.card G : R)) :
    Function.Injective (phiSub (R := R) (T := T) (A := A) (G := G) hact) := by
  intro x y hxy
  have h := congrArg (fun z => prj (R := R) (A := A) (G := G) hG
    ((z : ↥(FPS (R := T) (A := T ⊗[R] A) (G := G))) : T ⊗[R] A)) hxy
  simp only [phiSub_coe, prj_inkl] at h
  exact h

lemma phiSub_surjective (hact : ∀ (g : G) (t : T) (a : A), g • (t ⊗ₜ[R] a) = t ⊗ₜ[R] (g • a))
    (hG : IsUnit (Fintype.card G : R)) :
    Function.Surjective (phiSub (R := R) (T := T) (A := A) (G := G) hact) := by
  intro y
  refine ⟨prj (R := R) (A := A) (G := G) hG (y : T ⊗[R] A), ?_⟩
  apply Subtype.ext
  have hid := inkl_prj (R := R) (T := T) (A := A) (G := G) (hact := hact) hG (y : T ⊗[R] A)
  rw [phiSub_coe, hid]
  have hsum : (∑ g : G, g • (y : T ⊗[R] A)) = ((Fintype.card G : R)) • (y : T ⊗[R] A) := by
    rw [Finset.sum_congr rfl (fun g (_ : g ∈ Finset.univ) => y.2 g)]
    rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  rw [hsum, smul_smul, ABCBridge.FiniteEtaleFixedPoints.groupCardInv_mul_card, one_smul]

/-- **Fixed points commute with base change**, when the group order is invertible. -/
noncomputable def fixedPointsBaseChange (hact : ∀ (g : G) (t : T) (a : A), g • (t ⊗ₜ[R] a) = t ⊗ₜ[R] (g • a))
    (hG : IsUnit (Fintype.card G : R)) :
    T ⊗[R] ↥(FPS (R := R) (A := A) (G := G)) ≃ₐ[T]
      ↥(FPS (R := T) (A := T ⊗[R] A) (G := G)) :=
  AlgEquiv.ofBijective (phiSub (R := R) (T := T) (A := A) (G := G) hact)
    ⟨phiSub_injective hact hG, phiSub_surjective hact hG⟩

lemma fixedPointsBaseChange_tmul (hact : ∀ (g : G) (t : T) (a : A), g • (t ⊗ₜ[R] a) = t ⊗ₜ[R] (g • a))
    (hG : IsUnit (Fintype.card G : R)) (t : T) (b : ↥(FPS (R := R) (A := A) (G := G))) :
    ((fixedPointsBaseChange (R := R) (T := T) (A := A) (G := G) hact hG (t ⊗ₜ[R] b) :
      ↥(FPS (R := T) (A := T ⊗[R] A) (G := G))) : T ⊗[R] A) = t ⊗ₜ[R] (b : A) :=
  phiHom_tmul t b

end Main

end S1847Probe1
