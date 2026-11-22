import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Tactic

/-!
# Localized tensor reassociation

For an R-algebra A and elements t_i t_j : R, this file relates

  Away(t_i t_j) tensor over Away(t_i) with (Away(t_i) tensor over R with A)

to

  Away(t_i t_j) tensor over R with A.

The linear reassociation is supplied by the heterobasic cancellation
AlgebraTensorModule.cancelBaseChange.  The ring/algebra upgrade requires the
multiplicativity of that linear map; the precise obstruction is recorded at the
end.  No unconditional ring equivalence is asserted here.
-/

open scoped TensorProduct
open AlgebraicGeometry CategoryTheory

noncomputable section

namespace LeanFormal.IUT.Foundations.LocalizedTensorReassociation

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
variable (t_i t_j : R)

/-- The first away localization. -/
abbrev Ri : Type u := Localization.Away t_i

/-- The product away localization. -/
abbrev Rij : Type u := Localization.Away (t_i * t_j)

/-- The canonical ring hom from Away(t_i) to Away(t_i t_j). -/
noncomputable def riToRij : Ri (R := R) (t_i := t_i) →+* Rij (R := R) (t_i := t_i) (t_j := t_j) :=
  IsLocalization.Away.awayToAwayRight (R := R) (x := t_i) (y := t_j)
    (P := Rij (R := R) (t_i := t_i) (t_j := t_j))

/-- The canonical algebra structure of Away(t_i t_j) over Away(t_i). -/
noncomputable instance riAlgebraRij : Algebra (Ri (R := R) (t_i := t_i))
    (Rij (R := R) (t_i := t_i) (t_j := t_j)) :=
  (riToRij (R := R) (A := A) t_i t_j).toAlgebra

/-- The source of the reassociation: R_ij over R_i with R_i over R with A. -/
abbrev source : Type u :=
  TensorProduct (Ri (R := R) (t_i := t_i)) (Rij (R := R) (t_i := t_i) (t_j := t_j))
    (TensorProduct R (Ri (R := R) (t_i := t_i)) A)

/-- The target of the reassociation: R_ij over R with A. -/
abbrev target : Type u :=
  TensorProduct R (Rij (R := R) (t_i := t_i) (t_j := t_j)) A

/-- The heterobasic cancellation map, linear over R_ij. -/
noncomputable def localizedTensorReassociationLinear :
    source (R := R) (A := A) (t_i := t_i) (t_j := t_j) ≃ₗ[
      Rij (R := R) (t_i := t_i) (t_j := t_j)]
    target (R := R) (A := A) (t_i := t_i) (t_j := t_j) :=
  AlgebraTensorModule.cancelBaseChange R
    (Ri (R := R) (t_i := t_i))
    (Rij (R := R) (t_i := t_i) (t_j := t_j))
    (Rij (R := R) (t_i := t_i) (t_j := t_j))
    A

/-- The linear reassociation sends a pure nested tensor to the corresponding
cancelled tensor. -/
theorem localizedTensorReassociationLinear_tmul
    (m : Rij (R := R) (t_i := t_i) (t_j := t_j))
    (r : Ri (R := R) (t_i := t_i)) (a : A) :
    localizedTensorReassociationLinear (R := R) (A := A) (t_i := t_i) (t_j := t_j)
        (m ⊗ₜ (r ⊗ₜ a)) =
      (r • m) ⊗ₜ a := rfl

/-- The linear reassociation is an R_ij-linear equivalence. -/
theorem localizedTensorReassociationLinear_bijective :
    Function.Bijective
      (localizedTensorReassociationLinear (R := R) (A := A) (t_i := t_i) (t_j := t_j)) :=
  (localizedTensorReassociationLinear (R := R) (A := A) (t_i := t_i) (t_j := t_j)).bijective

/-- The linear reassociation has inverse. -/
noncomputable def localizedTensorReassociationLinearSymm :
    target (R := R) (A := A) (t_i := t_i) (t_j := t_j) ≃ₗ[
      Rij (R := R) (t_i := t_i) (t_j := t_j)]
    source (R := R) (A := A) (t_i := t_i) (t_j := t_j) :=
  (localizedTensorReassociationLinear (R := R) (A := A) (t_i := t_i) (t_j := t_j)).symm

/-- The inverse linear map sends a pure tensor to the nested pure tensor. -/
theorem localizedTensorReassociationLinearSymm_tmul
    (m : Rij (R := R) (t_i := t_i) (t_j := t_j)) (a : A) :
    localizedTensorReassociationLinearSymm (R := R) (A := A) (t_i := t_i) (t_j := t_j)
        (m ⊗ₜ a) =
      m ⊗ₜ ((1 : Ri (R := R) (t_i := t_i)) ⊗ₜ a) := rfl

/-- The pointwise multiplication condition needed to upgrade the linear
reassociation to a ring equivalence. -/
def LinearMapIsMultiplicative : Prop :=
  ∀ x y : source (R := R) (A := A) (t_i := t_i) (t_j := t_j),
    localizedTensorReassociationLinear (R := R) (A := A) (t_i := t_i) (t_j := t_j)
        (x * y) =
      localizedTensorReassociationLinear (R := R) (A := A) (t_i := t_i) (t_j := t_j) x *
        localizedTensorReassociationLinear (R := R) (A := A) (t_i := t_i) (t_j := t_j) y

/-- The unit condition needed to upgrade the linear reassociation. -/
def LinearMapPreservesOne : Prop :=
  localizedTensorReassociationLinear (R := R) (A := A) (t_i := t_i) (t_j := t_j) 1 = 1

/-- Conditional algebra equivalence: from the two ring-hom compatibility
conditions, the linear cancellation map becomes an R_ij-algebra equivalence. -/
noncomputable def localizedTensorReassociation
    (hone : LinearMapPreservesOne (R := R) (A := A) (t_i := t_i) (t_j := t_j))
    (hmul : LinearMapIsMultiplicative (R := R) (A := A) (t_i := t_i) (t_j := t_j)) :
    source (R := R) (A := A) (t_i := t_i) (t_j := t_j) ≃ₐ[
      Rij (R := R) (t_i := t_i) (t_j := t_j)]
    target (R := R) (A := A) (t_i := t_i) (t_j := t_j) :=
  AlgEquiv.ofLinearEquiv
    (localizedTensorReassociationLinear (R := R) (A := A) (t_i := t_i) (t_j := t_j))
    hone hmul

/-- The conditional algebra equivalence has the expected pure-tensor formula. -/
theorem localizedTensorReassociation_tmul
    (hone : LinearMapPreservesOne (R := R) (A := A) (t_i := t_i) (t_j := t_j))
    (hmul : LinearMapIsMultiplicative (R := R) (A := A) (t_i := t_i) (t_j := t_j))
    (m : Rij (R := R) (t_i := t_i) (t_j := t_j))
    (r : Ri (R := R) (t_i := t_i)) (a : A) :
    localizedTensorReassociation (R := R) (A := A) (t_i := t_i) (t_j := t_j) hone hmul
        (m ⊗ₜ (r ⊗ₜ a)) =
      (r • m) ⊗ₜ a := rfl

/-- The symmetric localized form: reversing the two away factors. -/
abbrev symmetricSource : Type u :=
  TensorProduct (Ri (R := R) (t_i := t_i)) (Rij (R := R) (t_i := t_i) (t_j := t_j))
    (TensorProduct R A (Ri (R := R) (t_i := t_i)))

/-- Symmetric linear reassociation. -/
noncomputable def symmetricLocalizedTensorReassociationLinear :
    symmetricSource (R := R) (A := A) (t_i := t_i) (t_j := t_j) ≃ₗ[
      Rij (R := R) (t_i := t_i) (t_j := t_j)]
    target (R := R) (A := A) (t_i := t_i) (t_j := t_j) :=
  (TensorProduct.comm (Ri (R := R) (t_i := t_i)) (Rij (R := R) (t_i := t_i) (t_j := t_j))
      (TensorProduct R A (Ri (R := R) (t_i := t_i)))).trans
    (localizedTensorReassociationLinear (R := R) (A := A) (t_i := t_i) (t_j := t_j))

/-- Symmetric ring compatibility condition. -/
def SymmetricLinearMapIsMultiplicative : Prop :=
  ∀ x y : symmetricSource (R := R) (A := A) (t_i := t_i) (t_j := t_j),
    symmetricLocalizedTensorReassociationLinear (R := R) (A := A) (t_i := t_i) (t_j := t_j)
        (x * y) =
      symmetricLocalizedTensorReassociationLinear (R := R) (A := A) (t_i := t_i) (t_j := t_j)
          x *
        symmetricLocalizedTensorReassociationLinear (R := R) (A := A) (t_i := t_i) (t_j := t_j)
          y

/-- Conditional symmetric algebra equivalence. -/
noncomputable def symmetricLocalizedTensorReassociation
    (hone : symmetricLocalizedTensorReassociationLinear (R := R) (A := A) (t_i := t_i) (t_j := t_j) 1 = 1)
    (hmul : SymmetricLinearMapIsMultiplicative (R := R) (A := A) (t_i := t_i) (t_j := t_j)) :
    symmetricSource (R := R) (A := A) (t_i := t_i) (t_j := t_j) ≃ₐ[
      Rij (R := R) (t_i := t_i) (t_j := t_j)]
    target (R := R) (A := A) (t_i := t_i) (t_j := t_j) :=
  AlgEquiv.ofLinearEquiv
    (symmetricLocalizedTensorReassociationLinear (R := R) (A := A) (t_i := t_i) (t_j := t_j))
    hone hmul

/-- Exact obstruction: the unconditional ring equivalence would follow from the
multiplicativity and unit conditions above.  Mathlib supplies the linear
heterobasic cancellation AlgebraTensorModule.cancelBaseChange, but the
algebra-version API IsPushout.cancelBaseChangeAlg requires an
Algebra.IsPushout square for the two away localizations, which is not
constructed here. -/
def ReassociationRingUpgradeResidual : Prop :=
  LinearMapPreservesOne (R := R) (A := A) (t_i := t_i) (t_j := t_j) ∧
    LinearMapIsMultiplicative (R := R) (A := A) (t_i := t_i) (t_j := t_j)

/-- The symmetric residual. -/
def SymmetricReassociationRingUpgradeResidual : Prop :=
  symmetricLocalizedTensorReassociationLinear (R := R) (A := A) (t_i := t_i) (t_j := t_j) 1 = 1 ∧
    SymmetricLinearMapIsMultiplicative (R := R) (A := A) (t_i := t_i) (t_j := t_j)

/-- The residual is exactly what upgrades the actual linear reassociation to
the requested ring equivalence. -/
theorem reassociation_of_residual
    (h : ReassociationRingUpgradeResidual (R := R) (A := A) (t_i := t_i) (t_j := t_j)) :
    Nonempty (source (R := R) (A := A) (t_i := t_i) (t_j := t_j) ≃ₐ[
      Rij (R := R) (t_i := t_i) (t_j := t_j)]
      target (R := R) (A := A) (t_i := t_i) (t_j := t_j)) :=
  ⟨localizedTensorReassociation (R := R) (A := A) (t_i := t_i) (t_j := t_j) h.1 h.2⟩

end LeanFormal.IUT.Foundations.LocalizedTensorReassociation
