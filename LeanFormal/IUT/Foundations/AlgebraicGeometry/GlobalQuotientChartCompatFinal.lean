import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartCompat
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Final inverse-law proofs for the affine-quotient base-change comparison

Both inverse laws are proved by exposing the right-hand identity as
`Spec.map (𝟙 _)`, applying `Spec.map_injective`, and then `CommRingCat.hom_ext`.
This is the final proof route requested after the `change` route failed.
-/
namespace ABCBridge.GlobalQuotientChartCompatFinal

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open ABCBridge.GlobalQuotientChartCompat

universe u

variable {R : Type u} [CommRing R] {A G : Type u} [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G] [MulSemiringAction G A] [SMulCommClass G R A]
  [Algebra.Etale R A] [Module.Finite R A]
  {R' : Type u} [CommRing R'] [Algebra R R'] [Module.Flat R R']

/-- Final proof of the first inverse law: the comparison hom followed by the
comparison inv is the identity. -/
theorem affineQuotientBaseChangeCoverHom_inv_final :
    affineQuotientBaseChangeCoverHom (R := R) (A := A) (G := G) (R' := R') ≫
        affineQuotientBaseChangeCoverInv (R := R) (A := A) (G := G) (R' := R') =
      𝟙 _ := by
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  show (Spec.map (CommRingCat.ofHom
      (affineQuotientBaseChangeAlgEquiv (R := R) (A := A) (G := G)
        (R' := R')).symm.toRingHom) :
      (affineQuotientBaseChangeCover (R := R) (A := A) (G := G) (R' := R')).carrier ⟶
        (affineQuotientBaseChangeActualCover (R := R) (A := A) (G := G) (R' := R')).carrier) ≫
      (Spec.map (CommRingCat.ofHom
        (affineQuotientBaseChangeAlgEquiv (R := R) (A := A) (G := G)
          (R' := R')).toRingHom) :
        (affineQuotientBaseChangeActualCover (R := R) (A := A) (G := G) (R' := R')).carrier ⟶
          (affineQuotientBaseChangeCover (R := R) (A := A) (G := G) (R' := R')).carrier) =
    𝟙 (affineQuotientBaseChangeCover (R := R) (A := A) (G := G) (R' := R')).carrier
  rw [← Spec.map_comp]
  conv_rhs => rw [← Spec.map_id]
  apply Spec.map_injective
  apply CommRingCat.hom_ext
  intro x
  simp

/-- Final proof of the second inverse law: the comparison inv followed by the
comparison hom is the identity. -/
theorem affineQuotientBaseChangeCoverInv_hom_final :
    affineQuotientBaseChangeCoverInv (R := R) (A := A) (G := G) (R' := R') ≫
        affineQuotientBaseChangeCoverHom (R := R) (A := A) (G := G) (R' := R') =
      𝟙 _ := by
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  show (Spec.map (CommRingCat.ofHom
      (affineQuotientBaseChangeAlgEquiv (R := R) (A := A) (G := G)
        (R' := R')).toRingHom) :
      (affineQuotientBaseChangeActualCover (R := R) (A := A) (G := G) (R' := R')).carrier ⟶
        (affineQuotientBaseChangeCover (R := R) (A := A) (G := G) (R' := R')).carrier) ≫
      (Spec.map (CommRingCat.ofHom
        (affineQuotientBaseChangeAlgEquiv (R := R) (A := A) (G := G)
          (R' := R')).symm.toRingHom) :
        (affineQuotientBaseChangeCover (R := R) (A := A) (G := G) (R' := R')).carrier ⟶
          (affineQuotientBaseChangeActualCover (R := R) (A := A) (G := G) (R' := R')).carrier) =
    𝟙 (affineQuotientBaseChangeActualCover (R := R) (A := A) (G := G) (R' := R')).carrier
  rw [← Spec.map_comp]
  conv_rhs => rw [← Spec.map_id]
  apply Spec.map_injective
  apply CommRingCat.hom_ext
  intro x
  simp

/-- The final comparison isomorphism, packaged from the two final inverse
laws. -/
noncomputable def affineQuotientBaseChangeCoverEquivFinal :
    affineQuotientBaseChangeCover (R := R) (A := A) (G := G) (R' := R') ≅
      affineQuotientBaseChangeActualCover (R := R) (A := A) (G := G) (R' := R') where
  hom := affineQuotientBaseChangeCoverHom (R := R) (A := A) (G := G) (R' := R')
  inv := affineQuotientBaseChangeCoverInv (R := R) (A := A) (G := G) (R' := R')
  hom_inv_id := affineQuotientBaseChangeCoverHom_inv_final (R := R) (A := A) (G := G) (R' := R')
  inv_hom_id := affineQuotientBaseChangeCoverInv_hom_final (R := R) (A := A) (G := G) (R' := R')

/-- The hom component of the final comparison is the production hom. -/
theorem affineQuotientBaseChangeCoverEquivFinal_hom :
    (affineQuotientBaseChangeCoverEquivFinal (R := R) (A := A) (G := G) (R' := R')).hom =
      affineQuotientBaseChangeCoverHom (R := R) (A := A) (G := G) (R' := R') :=
  rfl

/-- The inv component of the final comparison is the production inv. -/
theorem affineQuotientBaseChangeCoverEquivFinal_inv :
    (affineQuotientBaseChangeCoverEquivFinal (R := R) (A := A) (G := G) (R' := R')).inv =
      affineQuotientBaseChangeCoverInv (R := R) (A := A) (G := G) (R' := R') :=
  rfl

/-- The final comparison satisfies the first inverse law. -/
theorem affineQuotientBaseChangeCoverEquivFinal_hom_inv_id :
    (affineQuotientBaseChangeCoverEquivFinal (R := R) (A := A) (G := G) (R' := R')).hom ≫
        (affineQuotientBaseChangeCoverEquivFinal (R := R) (A := A) (G := G) (R' := R')).inv =
      𝟙 _ :=
  (affineQuotientBaseChangeCoverEquivFinal (R := R) (A := A) (G := G) (R' := R')).hom_inv_id

/-- The final comparison satisfies the second inverse law. -/
theorem affineQuotientBaseChangeCoverEquivFinal_inv_hom_id :
    (affineQuotientBaseChangeCoverEquivFinal (R := R) (A := A) (G := G) (R' := R')).inv ≫
        (affineQuotientBaseChangeCoverEquivFinal (R := R) (A := A) (G := G) (R' := R')).hom =
      𝟙 _ :=
  (affineQuotientBaseChangeCoverEquivFinal (R := R) (A := A) (G := G) (R' := R')).inv_hom_id

/-- Final hom-inverse law in point-free form. -/
theorem affineQuotientBaseChangeCoverHom_inv_final' :
    affineQuotientBaseChangeCoverHom (R := R) (A := A) (G := G) (R' := R') ≫
        affineQuotientBaseChangeCoverInv (R := R) (A := A) (G := G) (R' := R') =
      𝟙 _ :=
  affineQuotientBaseChangeCoverHom_inv_final (R := R) (A := A) (G := G) (R' := R')

/-- Final inv-hom law in point-free form. -/
theorem affineQuotientBaseChangeCoverInv_hom_final' :
    affineQuotientBaseChangeCoverInv (R := R) (A := A) (G := G) (R' := R') ≫
        affineQuotientBaseChangeCoverHom (R := R) (A := A) (G := G) (R' := R') =
      𝟙 _ :=
  affineQuotientBaseChangeCoverInv_hom_final (R := R) (A := A) (G := G) (R' := R')


section FinalConsequences

/-- First inverse law with a post-composed morphism. -/
theorem affineQuotientBaseChangeCoverHom_inv_final_assoc
    {Z : Scheme.{u}}
    (f : (affineQuotientBaseChangeCover (R := R) (A := A) (G := G) (R' := R')).carrier ⟶ Z) :
    (affineQuotientBaseChangeCoverHom (R := R) (A := A) (G := G) (R' := R') ≫
        affineQuotientBaseChangeCoverInv (R := R) (A := A) (G := G) (R' := R')) ≫ f = f := by
  rw [affineQuotientBaseChangeCoverHom_inv_final]
  exact Category.id_comp f

/-- Second inverse law with a post-composed morphism. -/
theorem affineQuotientBaseChangeCoverInv_hom_final_assoc
    {Z : Scheme.{u}}
    (f : (affineQuotientBaseChangeActualCover (R := R) (A := A) (G := G) (R' := R')).carrier ⟶ Z) :
    (affineQuotientBaseChangeCoverInv (R := R) (A := A) (G := G) (R' := R') ≫
        affineQuotientBaseChangeCoverHom (R := R) (A := A) (G := G) (R' := R')) ≫ f = f := by
  rw [affineQuotientBaseChangeCoverInv_hom_final]
  exact Category.id_comp f

/-- First inverse law of the final packaged comparison, post-composed. -/
theorem affineQuotientBaseChangeCoverEquivFinal_hom_inv_id_assoc
    {Z : Scheme.{u}}
    (f : (affineQuotientBaseChangeCover (R := R) (A := A) (G := G) (R' := R')).carrier ⟶ Z) :
    ((affineQuotientBaseChangeCoverEquivFinal (R := R) (A := A) (G := G) (R' := R')).hom ≫
        (affineQuotientBaseChangeCoverEquivFinal (R := R) (A := A) (G := G) (R' := R')).inv) ≫
      f = f := by
  rw [(affineQuotientBaseChangeCoverEquivFinal (R := R) (A := A) (G := G) (R' := R')).hom_inv_id]
  exact Category.id_comp f

/-- Second inverse law of the final packaged comparison, post-composed. -/
theorem affineQuotientBaseChangeCoverEquivFinal_inv_hom_id_assoc
    {Z : Scheme.{u}}
    (f : (affineQuotientBaseChangeActualCover (R := R) (A := A) (G := G) (R' := R')).carrier ⟶ Z) :
    ((affineQuotientBaseChangeCoverEquivFinal (R := R) (A := A) (G := G) (R' := R')).inv ≫
        (affineQuotientBaseChangeCoverEquivFinal (R := R) (A := A) (G := G) (R' := R')).hom) ≫
      f = f := by
  rw [(affineQuotientBaseChangeCoverEquivFinal (R := R) (A := A) (G := G) (R' := R')).inv_hom_id]
  exact Category.id_comp f

/-- The final comparison is an isomorphism of finite etale covers, with both
inverse laws proved. -/
theorem affineQuotientBaseChangeCoverEquivFinal_isIso :
    IsIso (affineQuotientBaseChangeCoverEquivFinal (R := R) (A := A) (G := G) (R' := R')).hom :=
  inferInstance

/-- The inverse comparison is also an isomorphism. -/
theorem affineQuotientBaseChangeCoverEquivFinal_inv_isIso :
    IsIso (affineQuotientBaseChangeCoverEquivFinal (R := R) (A := A) (G := G) (R' := R')).inv :=
  inferInstance

/-- The two final laws are available as a conjunction for consumers. -/
theorem affineQuotientBaseChangeCoverEquivFinal_inverse_laws :
    ((affineQuotientBaseChangeCoverEquivFinal (R := R) (A := A) (G := G) (R' := R')).hom ≫
        (affineQuotientBaseChangeCoverEquivFinal (R := R) (A := A) (G := G) (R' := R')).inv =
      𝟙 _) ∧
      ((affineQuotientBaseChangeCoverEquivFinal (R := R) (A := A) (G := G) (R' := R')).inv ≫
        (affineQuotientBaseChangeCoverEquivFinal (R := R) (A := A) (G := G) (R' := R')).hom =
      𝟙 _) :=
  ⟨(affineQuotientBaseChangeCoverEquivFinal (R := R) (A := A) (G := G) (R' := R')).hom_inv_id,
    (affineQuotientBaseChangeCoverEquivFinal (R := R) (A := A) (G := G) (R' := R')).inv_hom_id⟩

end FinalConsequences

end ABCBridge.GlobalQuotientChartCompatFinal
