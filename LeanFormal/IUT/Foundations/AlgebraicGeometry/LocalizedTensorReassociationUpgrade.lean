import LeanFormal.IUT.Foundations.AlgebraicGeometry.AwayImageLocalizationInstance
import LeanFormal.IUT.Foundations.AlgebraicGeometry.LocalizedTensorReassociation
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic

/-!
# Unconditional localized tensor reassociation

Using the constructed product-localization pushout, this file builds the actual
R_ij-algebra equivalence

  R_ij tensor over R_i with (R_i tensor over R A)
    ~= R_ij tensor over R with A

by the algebra associator and the cancellation of R_i.  The symmetric form is
obtained by tensor commutativity.  The pure-tensor formula is recorded, and the
remaining ring-upgrade residual is rewritten in terms of the actual equivalence.
-/

open scoped TensorProduct
open AlgebraicGeometry CategoryTheory

noncomputable section

namespace LeanFormal.IUT.Foundations.LocalizedTensorReassociationUpgrade

universe u

open LeanFormal.IUT.Foundations.LocalizedTensorReassociation
open LeanFormal.IUT.Foundations.AwayAwayPushout
open LeanFormal.IUT.Foundations.AwayImageLocalizationInstance

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
variable (t_i t_j : R)

/-- The first away localization. -/
abbrev Ri : Type u := Localization.Away t_i

/-- The product away localization. -/
abbrev Rij : Type u := Localization.Away (t_i * t_j)

/-- The algebra equivalence from the nested tensor to the associated tensor. -/
noncomputable def reassociationAssoc :
    LocalizedTensorReassociation.source (R := R) (A := A) (t_i := t_i) (t_j := t_j) ≃ₐ[
      Rij (R := R) (t_i := t_i) (t_j := t_j)]
    TensorProduct (TensorProduct (Ri (R := R) (t_i := t_i))
      (Rij (R := R) (t_i := t_i) (t_j := t_j))
      (Ri (R := R) (t_i := t_i))) R A :=
  (Algebra.TensorProduct.assoc (R := R)
    (S := Ri (R := R) (t_i := t_i))
    (T := Rij (R := R) (t_i := t_i) (t_j := t_j))
    (A := Rij (R := R) (t_i := t_i) (t_j := t_j))
    (C := Ri (R := R) (t_i := t_i)) (D := A)).symm

/-- The cancellation of the inner R_i tensor factor. -/
noncomputable def reassociationCancel :
    TensorProduct (TensorProduct (Ri (R := R) (t_i := t_i))
      (Rij (R := R) (t_i := t_i) (t_j := t_j))
      (Ri (R := R) (t_i := t_i))) R A ≃ₐ[
        Rij (R := R) (t_i := t_i) (t_j := t_j)]
      LocalizedTensorReassociation.target (R := R) (A := A) (t_i := t_i) (t_j := t_j) :=
  Algebra.TensorProduct.congr (R := R)
    (S := Rij (R := R) (t_i := t_i) (t_j := t_j))
    (A := TensorProduct (Ri (R := R) (t_i := t_i))
      (Rij (R := R) (t_i := t_i) (t_j := t_j))
      (Ri (R := R) (t_i := t_i)))
    (B := A) (C := Rij (R := R) (t_i := t_i) (t_j := t_j)) (D := A)
    (Algebra.TensorProduct.rid (R := Ri (R := R) (t_i := t_i))
      (S := Rij (R := R) (t_i := t_i) (t_j := t_j))
      (A := Rij (R := R) (t_i := t_i) (t_j := t_j)))
    (AlgEquiv.refl R A)

/-- The unconditional R_ij-algebra reassociation equivalence. -/
noncomputable def localizedTensorReassociationUnconditional :
    LocalizedTensorReassociation.source (R := R) (A := A) (t_i := t_i) (t_j := t_j) ≃ₐ[
      Rij (R := R) (t_i := t_i) (t_j := t_j)]
      LocalizedTensorReassociation.target (R := R) (A := A) (t_i := t_i) (t_j := t_j) :=
  (reassociationAssoc (R := R) (A := A) (t_i := t_i) (t_j := t_j)).trans
    (reassociationCancel (R := R) (A := A) (t_i := t_i) (t_j := t_j))

/-- The unconditional reassociation packaged as a ring equivalence. -/
noncomputable def localizedTensorReassociationRing :
    LocalizedTensorReassociation.source (R := R) (A := A) (t_i := t_i) (t_j := t_j) ≃+*
      LocalizedTensorReassociation.target (R := R) (A := A) (t_i := t_i) (t_j := t_j) :=
  (localizedTensorReassociationUnconditional (R := R) (A := A) (t_i := t_i) (t_j := t_j)).toRingEquiv

/-- Pure-tensor formula for the unconditional reassociation. -/
theorem localizedTensorReassociationUnconditional_tmul
    (m : Rij (R := R) (t_i := t_i) (t_j := t_j))
    (r : Ri (R := R) (t_i := t_i)) (a : A) :
    localizedTensorReassociationUnconditional (R := R) (A := A) (t_i := t_i) (t_j := t_j)
        (m ⊗ₜ (r ⊗ₜ a)) =
      (r • m) ⊗ₜ a := by
  simp [localizedTensorReassociationUnconditional, reassociationAssoc, reassociationCancel,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.rid_tmul,
    Algebra.TensorProduct.assoc_tmul]

/-- The inverse pure-tensor formula. -/
theorem localizedTensorReassociationUnconditional_symm_tmul
    (m : Rij (R := R) (t_i := t_i) (t_j := t_j)) (a : A) :
    (localizedTensorReassociationUnconditional (R := R) (A := A) (t_i := t_i) (t_j := t_j)).symm
        (m ⊗ₜ a) =
      (m ⊗ₜ (1 : Ri (R := R) (t_i := t_i))) ⊗ₜ a := by
  simp [localizedTensorReassociationUnconditional, reassociationAssoc, reassociationCancel,
    Algebra.TensorProduct.congr_symm_apply, Algebra.TensorProduct.rid_symm_apply,
    Algebra.TensorProduct.assoc_symm_tmul]

/-- Symmetric source: the two away factors are reversed. -/
abbrev symmetricSource : Type u :=
  LocalizedTensorReassociation.symmetricSource (R := R) (A := A) (t_i := t_i) (t_j := t_j)

/-- Symmetric associator for the reversed source. -/
noncomputable def symmetricReassociationAssoc :
    symmetricSource (R := R) (A := A) (t_i := t_i) (t_j := t_j) ≃ₐ[
      Rij (R := R) (t_i := t_i) (t_j := t_j)]
    TensorProduct (TensorProduct (Ri (R := R) (t_i := t_i))
      (Rij (R := R) (t_i := t_i) (t_j := t_j))
      (Ri (R := R) (t_i := t_i))) R A :=
  (TensorProduct.comm
    (TensorProduct (Ri (R := R) (t_i := t_i)) (Rij (R := R) (t_i := t_i) (t_j := t_j))
      (TensorProduct R A (Ri (R := R) (t_i := t_i))))
    R A).trans
    (reassociationAssoc (R := R) (A := A) (t_i := t_i) (t_j := t_j))

/-- Symmetric unconditional reassociation. -/
noncomputable def symmetricLocalizedTensorReassociationUnconditional :
    symmetricSource (R := R) (A := A) (t_i := t_i) (t_j := t_j) ≃ₐ[
      Rij (R := R) (t_i := t_i) (t_j := t_j)]
      LocalizedTensorReassociation.target (R := R) (A := A) (t_i := t_i) (t_j := t_j) :=
  (symmetricReassociationAssoc (R := R) (A := A) (t_i := t_i) (t_j := t_j)).trans
    (reassociationCancel (R := R) (A := A) (t_i := t_i) (t_j := t_j))

/-- Symmetric unconditional ring equivalence. -/
noncomputable def symmetricLocalizedTensorReassociationRing :
    symmetricSource (R := R) (A := A) (t_i := t_i) (t_j := t_j) ≃+*
      LocalizedTensorReassociation.target (R := R) (A := A) (t_i := t_i) (t_j := t_j) :=
  (symmetricLocalizedTensorReassociationUnconditional (R := R) (A := A)
    (t_i := t_i) (t_j := t_j)).toRingEquiv

/-- The unit condition for the original linear reassociation follows from the
constructed algebra equivalence. -/
theorem reassociation_linear_preserves_one :
    LinearMapPreservesOne (R := R) (A := A) (t_i := t_i) (t_j := t_j) := by
  change localizedTensorReassociationLinear (R := R) (A := A) (t_i := t_i) (t_j := t_j) 1 = 1
  rw [show localizedTensorReassociationLinear (R := R) (A := A) (t_i := t_i) (t_j := t_j) =
      (localizedTensorReassociationUnconditional (R := R) (A := A)
        (t_i := t_i) (t_j := t_j)).toLinearEquiv from rfl]
  exact map_one _

/-- The multiplicativity condition for the original linear reassociation follows
from the constructed algebra equivalence. -/
theorem reassociation_linear_is_multiplicative :
    LinearMapIsMultiplicative (R := R) (A := A) (t_i := t_i) (t_j := t_j) := by
  intro x y
  change localizedTensorReassociationLinear (R := R) (A := A) (t_i := t_i) (t_j := t_j)
      (x * y) =
    localizedTensorReassociationLinear (R := R) (A := A) (t_i := t_i) (t_j := t_j) x *
      localizedTensorReassociationLinear (R := R) (A := A) (t_i := t_i) (t_j := t_j) y
  rw [show localizedTensorReassociationLinear (R := R) (A := A) (t_i := t_i) (t_j := t_j) =
      (localizedTensorReassociationUnconditional (R := R) (A := A)
        (t_i := t_i) (t_j := t_j)).toLinearEquiv from rfl]
  exact map_mul _ x y

/-- The original ring-upgrade residual is closed. -/
theorem reassociationRingUpgradeResidual_closed :
    ReassociationRingUpgradeResidual (R := R) (A := A) (t_i := t_i) (t_j := t_j) :=
  ⟨reassociation_linear_preserves_one (R := R) (A := A) (t_i := t_i) (t_j := t_j),
    reassociation_linear_is_multiplicative (R := R) (A := A) (t_i := t_i) (t_j := t_j)⟩

/-- The closed residual gives the original unconditional algebra equivalence. -/
noncomputable def localizedTensorReassociationClosed :
    LocalizedTensorReassociation.source (R := R) (A := A) (t_i := t_i) (t_j := t_j) ≃ₐ[
      Rij (R := R) (t_i := t_i) (t_j := t_j)]
      LocalizedTensorReassociation.target (R := R) (A := A) (t_i := t_i) (t_j := t_j) :=
  LocalizedTensorReassociation.localizedTensorReassociation
    (R := R) (A := A) (t_i := t_i) (t_j := t_j)
    (reassociationRingUpgradeResidual_closed (R := R) (A := A)
      (t_i := t_i) (t_j := t_j)).1
    (reassociationRingUpgradeResidual_closed (R := R) (A := A)
      (t_i := t_i) (t_j := t_j)).2


namespace LeanFormal.IUT.Foundations.LocalizedTensorReassociationUpgrade

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
variable (t_i t_j : R)

/-- The ring equivalence is the underlying ring equivalence of the algebra
equivalence. -/
theorem localizedTensorReassociationRing_toRingEquiv :
    localizedTensorReassociationRing (R := R) (A := A) (t_i := t_i) (t_j := t_j) =
      (localizedTensorReassociationUnconditional (R := R) (A := A)
        (t_i := t_i) (t_j := t_j)).toRingEquiv := rfl

/-- The symmetric ring equivalence is the underlying ring equivalence of the
symmetric algebra equivalence. -/
theorem symmetricLocalizedTensorReassociationRing_toRingEquiv :
    symmetricLocalizedTensorReassociationRing (R := R) (A := A) (t_i := t_i) (t_j := t_j) =
      (symmetricLocalizedTensorReassociationUnconditional (R := R) (A := A)
        (t_i := t_i) (t_j := t_j)).toRingEquiv := rfl

/-- The unconditional reassociation is surjective. -/
theorem localizedTensorReassociationUnconditional_surjective :
    Function.Surjective (localizedTensorReassociationUnconditional (R := R) (A := A)
      (t_i := t_i) (t_j := t_j)) :=
  (localizedTensorReassociationUnconditional (R := R) (A := A)
    (t_i := t_i) (t_j := t_j)).surjective

/-- The unconditional reassociation is injective. -/
theorem localizedTensorReassociationUnconditional_injective :
    Function.Injective (localizedTensorReassociationUnconditional (R := R) (A := A)
      (t_i := t_i) (t_j := t_j)) :=
  (localizedTensorReassociationUnconditional (R := R) (A := A)
    (t_i := t_i) (t_j := t_j)).injective

/-- The unconditional reassociation is bijective. -/
theorem localizedTensorReassociationUnconditional_bijective :
    Function.Bijective (localizedTensorReassociationUnconditional (R := R) (A := A)
      (t_i := t_i) (t_j := t_j)) :=
  (localizedTensorReassociationUnconditional (R := R) (A := A)
    (t_i := t_i) (t_j := t_j)).bijective

/-- The symmetric unconditional reassociation is bijective. -/
theorem symmetricLocalizedTensorReassociationUnconditional_bijective :
    Function.Bijective (symmetricLocalizedTensorReassociationUnconditional (R := R) (A := A)
      (t_i := t_i) (t_j := t_j)) :=
  (symmetricLocalizedTensorReassociationUnconditional (R := R) (A := A)
    (t_i := t_i) (t_j := t_j)).bijective

end LeanFormal.IUT.Foundations.LocalizedTensorReassociationUpgrade

end LeanFormal.IUT.Foundations.LocalizedTensorReassociationUpgrade
