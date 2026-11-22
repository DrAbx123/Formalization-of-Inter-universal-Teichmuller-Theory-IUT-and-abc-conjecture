/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1847

# S1847: fixed points commute with base change R' -> Omega (field 5 of S1835)

S1835 reduced the fifth field of the six-field geometric fibre functor at the closed
point (0,0) to the single statement

  S1835BCPreservesQuotients :
    forall (G : Type) [Group G] [Finite G],
      PreservesColimitsOfShape (SingleObj G) (S1835BC).op,

i.e. that the base change R' -> Omega commutes with taking G-fixed points (quotients by
finite groups) of finite etale R'-algebras.

## What is proved here (unconditionally)

1. The mathematical core of field 5, in the sharpest form (`fixedPointsBaseChange`):

   if G is a finite group acting on a commutative ring A by ring automorphisms and the
   order of G is invertible in the base ring R, then for EVERY R-algebra T the canonical
   map

     T (x)_R A^G  ->  (T (x)_R A)^G

   is an isomorphism.  No flatness of T is used.  Injectivity comes from the Reynolds
   retraction A -> A^G (which exhibits A^G as a direct summand of A as R-modules, hence
   survives - (x)_R T), and surjectivity from averaging a lift along T
   (`inkl_prj`, `prj_inkl`, `phiHom_mem`, `fixedPointsBaseChange`,
   `fixedPointsBaseChange_tmul`).

   The proof needs no hypothesis on R beyond the invertibility of the group order, and no
   hypothesis at all on T.  This is exactly the algebraic content of field 5; the
   classical field-case proofs (S1769/S1806) obtained it from flatness of K -> Kbar,
   which is unavailable for the closed point R' -> Omega.

2. At R' the hypothesis is available: `isUnit_card_R'` proves that the order of any
   finite group is a unit of R', because R' is an algebra over the number field
   F' = S1779K and Nat.card G is a unit of F'.

3. The instance-level comparison needed to feed (1) into the invariants cone of S1830G2:
   the group action on the base change induced by the functor `S1835BC` and the
   tensor-product action on `Omega (x)_{R'} A` agree on pure tensors
   (`actionMap_bc`, `bc_action_tmul`, `smul_bc_eq_tensor`) and hence define the SAME
   fixed-point subalgebra (`fps_bc_eq_tensor`).

4. The resulting isomorphism of fixed-point algebras `fpbc` (and its value on pure
   tensors, `fpbc_tmul`) between `Omega (x)_{R'} A^G` and `(Omega (x)_{R'} A)^G`.

## Exact first missing

What is NOT done here is the final purely categorical assembly: deriving

  S1835BCPreservesQuotients

from `fpbc`.  Concretely the first missing step is the linearity of `fpbc` on all
elements,

  forall y, (fpbc K y : Omega (x)_{R'} A) = Algebra.TensorProduct.map id incl y

(an immediate `TensorProduct.induction_on` consequence of `fpbc_tmul`, about ten lines),
followed by the mechanical construction of the isomorphism of cones
`invariantsCone (K >>> S1835BC) <-> S1835BC.mapCone (invariantsCone K)` and
`IsLimit.ofIsoLimit` along `S1830G2.invariantsIsLimit`.  Nothing mathematical is missing
at that point; the obstruction encountered here is only elaboration-level: the two
presentations of the fixed-point subalgebra (`FixedPoints.subalgebra` with the
tensor-product action versus with the functor action of `S1830G2`) live at types that are
definitionally equal through the abbrev `actionAlgebra` but are not syntactically equal,
so `Subalgebra.equivOfEq` can transport the algebras (`fpbc`) but the resulting terms do
not elaborate directly as the point of the S1830G2 cone.

## Honest boundary

No sorry, admit, new axiom, Shrink, ULift or PUnit occurs in this file.  Every
declaration depends only on propext, Classical.choice and Quot.sound (see the audit at
the end).  The statements proved are not weakened versions of field 5: (1) is strictly
stronger than what field 5 needs (arbitrary base change instead of R' -> Omega).
-/

import tmp.sheaf.xif.paper.S1835FiberRPrimeActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleFixedPoints
import LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorEqualizerFixedPoints
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
import Mathlib.RingTheory.Etale.Pi

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.defProp false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual.S1779FiniteEtaleClosure
open LeanFormal.IUT.XiFPaper.S1830G2G3RPrimeActual
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1835FiberRPrimeActual

namespace LeanFormal.IUT.XiFPaper.S1847RPrimeQuotientsActual

attribute [local instance] S1779PointClosureAlgebra

section Main

variable {R T A G : Type}
  [CommRing R] [CommRing T] [Algebra R T]
  [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G R A]

variable [instT : MulSemiringAction G (T ⊗[R] A)] [instC : SMulCommClass G T (T ⊗[R] A)]

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


/-! ## 2. The action of G on the base change -/

section BaseChangeAction

variable {G : Type} [Group G] [Fintype G]

/-- The action map of a base-changed action diagram is the tensor product of the identity
with the original action map. -/
lemma actionMap_bc (K : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} S1779R) (g : G) :
    S1830G2.actionMap (K ⋙ S1835BC) g =
      Algebra.TensorProduct.map (AlgHom.id S1835Omega S1835Omega)
        (S1830G2.actionMap K g) := rfl

/-- The S1830G2 action on the base change acts through the action on the second factor. -/
lemma bc_action_tmul (K : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} S1779R)
    (g : G) (t : S1835Omega) (a : S1830G2.actionAlgebra K) :
    (S1830G2.actionMulSemiringAction (F := K ⋙ S1835BC)).smul g (t ⊗ₜ[S1779R] a) =
      t ⊗ₜ[S1779R] ((S1830G2.actionMulSemiringAction (F := K)).smul g a) := by
  change S1830G2.actionMap (K ⋙ S1835BC) g⁻¹ (t ⊗ₜ[S1779R] a) =
    t ⊗ₜ[S1779R] (S1830G2.actionMap K g⁻¹ a)
  change (Algebra.TensorProduct.map (AlgHom.id S1835Omega S1835Omega) (S1830G2.actionMap K g⁻¹))
      (t ⊗ₜ[S1779R] a) = t ⊗ₜ[S1779R] (S1830G2.actionMap K g⁻¹ a)
  rw [Algebra.TensorProduct.map_tmul]
  simp

/-- The tensor-product action agrees with the S1830G2 action on the base change. -/
lemma smul_bc_eq_tensor (K : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} S1779R)
    (g : G) (x : S1835Omega ⊗[S1779R] S1830G2.actionAlgebra K) :
    (S1830G2.actionMulSemiringAction (F := K ⋙ S1835BC)).smul g x =
      (TensorEqualizerFixedPoints.tensorMulSemiringAction S1779R
        (S1830G2.actionAlgebra K) G S1835Omega).smul g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t a =>
      rw [bc_action_tmul]
  | add x y hx hy => simp only [smul_add, hx, hy]

/-- The two fixed point subalgebras of the base change (for the functor action and for the
tensor product action) coincide. -/
lemma fps_bc_eq_tensor (K : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} S1779R) :
    (FixedPoints.subalgebra S1835Omega (S1835Omega ⊗[S1779R] S1830G2.actionAlgebra K) G)
      = (FixedPoints.subalgebra S1835Omega
          (S1830G2.actionAlgebra (K ⋙ S1835BC)) G) := by
  apply Subalgebra.ext
  intro x
  change (∀ g : G, (TensorEqualizerFixedPoints.tensorMulSemiringAction S1779R
      (S1830G2.actionAlgebra K) G S1835Omega).smul g x = x) ↔
    (∀ g : G, (S1830G2.actionMulSemiringAction (F := K ⋙ S1835BC)).smul g x = x)
  exact forall_congr' (fun g => by rw [smul_bc_eq_tensor])

end BaseChangeAction


/-! ## 3. The fixed points of the base change -/

section Main

variable {G : Type} [Group G] [Fintype G]

/-- The order of a finite group is a unit of R'. -/
theorem isUnit_natCard_R' [Finite G] : IsUnit (Nat.card G : S1779R) := by
  haveI : Fintype G := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card]
  have hK : IsUnit (Fintype.card G : S1779K) :=
    IsUnit.mk0 _ (Nat.cast_ne_zero.mpr (Fintype.card_pos (α := G)).ne')
  obtain ⟨u, hu⟩ := hK
  refine ⟨Units.map (algebraMap S1779K S1779R).toMonoidHom u, ?_⟩
  show algebraMap S1779K S1779R ((u : S1779K)) = ((Fintype.card G : S1779R))
  rw [hu, map_natCast]

/-- The order of a finite group is a unit of R'. -/
theorem isUnit_card_R' : IsUnit (Fintype.card G : S1779R) := by
  haveI : Finite G := Finite.of_fintype G
  rw [← Nat.card_eq_fintype_card]
  exact isUnit_natCard_R' (G := G)

/-- Fixed points commute with the base change R' -> Omega: the canonical isomorphism from
the base change of the fixed point subalgebra to the fixed points of the base change. -/
noncomputable def fpbc (K : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} S1779R) :
    S1835Omega ⊗[S1779R] ↥(fixedPointSubalgebra S1779R (S1830G2.actionAlgebra K) G) ≃ₐ[S1835Omega]
      ↥(ABCBridge.FiniteEtaleFixedPoints.fixedPointSubalgebra S1835Omega
        (S1835Omega ⊗[S1779R] S1830G2.actionAlgebra K) G) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl)
      (Subalgebra.equivOfEq (fixedPointSubalgebra S1779R (S1830G2.actionAlgebra K) G)
        (ABCBridge.FiniteEtaleFixedPoints.fixedPointSubalgebra S1779R
          (S1830G2.actionAlgebra K) G) rfl)).trans
    (fixedPointsBaseChange (R := S1779R) (T := S1835Omega) (A := S1830G2.actionAlgebra K) (G := G)
      (instT := TensorEqualizerFixedPoints.tensorMulSemiringAction S1779R
        (S1830G2.actionAlgebra K) G S1835Omega)
      (instC := TensorEqualizerFixedPoints.tensorSMulCommClass S1779R
        (S1830G2.actionAlgebra K) G S1835Omega)
      (fun g t a => TensorEqualizerFixedPoints.tensor_smul_tmul (R := S1779R) (A := S1830G2.actionAlgebra K)
        (G := G) (T := S1835Omega) (g := g) (t := t) (a := a))
      (isUnit_card_R' (G := G)))

/-- The underlying element of the fixed-point base change on a pure tensor. -/
lemma fpbc_tmul (K : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} S1779R)
    (t : S1835Omega) (b : ↥(fixedPointSubalgebra S1779R (S1830G2.actionAlgebra K) G)) :
    (↑(fpbc (G := G) K (t ⊗ₜ[S1779R] b)) : S1835Omega ⊗[S1779R] S1830G2.actionAlgebra K) =
      t ⊗ₜ[S1779R] (b : S1830G2.actionAlgebra K) := by
  unfold fpbc
  rw [AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    fixedPointsBaseChange_tmul]
  rfl
end Main

/-! ## 5. Axiom audit -/

#print axioms S1847RPrimeQuotientsActual.inkl_prj
#print axioms S1847RPrimeQuotientsActual.prj_inkl
#print axioms S1847RPrimeQuotientsActual.phiHom_mem
#print axioms S1847RPrimeQuotientsActual.fixedPointsBaseChange
#print axioms S1847RPrimeQuotientsActual.fixedPointsBaseChange_tmul
#print axioms actionMap_bc
#print axioms bc_action_tmul
#print axioms smul_bc_eq_tensor
#print axioms fps_bc_eq_tensor
#print axioms isUnit_card_R'
#print axioms fpbc
#print axioms fpbc_tmul

end LeanFormal.IUT.XiFPaper.S1847RPrimeQuotientsActual