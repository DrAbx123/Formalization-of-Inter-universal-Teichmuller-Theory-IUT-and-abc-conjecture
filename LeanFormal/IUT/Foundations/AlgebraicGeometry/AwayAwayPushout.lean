import LeanFormal.IUT.Foundations.AlgebraicGeometry.AwayLocalizationPushout
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.Tactic

/-!
# Pushout square for two away localizations

For elements t_i t_j : R this file relates Away(t_i), Away(t_j), and
Away(t_i t_j).  It constructs the actual tensor-product localization
Away(t_i) tensor_R Away(t_j), the canonical maps to Away(t_i t_j), and the
pushout square conditional on the canonical localization instance at the image
of t_i.  The precise missing Mathlib instance is recorded explicitly.
-/

open scoped TensorProduct
open AlgebraicGeometry CategoryTheory

noncomputable section

namespace LeanFormal.IUT.Foundations.AwayAwayPushout

universe u

variable (R : Type u) [CommRing R] (t_i t_j : R)

/-- Localization away from t_i. -/
abbrev Ri : Type u := Localization.Away t_i

/-- Localization away from t_j. -/
abbrev Rj : Type u := Localization.Away t_j

/-- Localization away from the product t_i t_j. -/
abbrev Rij : Type u := Localization.Away (t_i * t_j)

/-- The tensor-product localization at t_i and t_j. -/
abbrev RijTensor : Type u := TensorProduct R (Ri (R := R) (t_i := t_i)) (Rj (R := R) (t_j := t_j))

/-- The canonical map R_j to R_ij; it inverts t_i in R_j. -/
noncomputable def rjToRij : Rj (R := R) (t_j := t_j) →+* Rij (R := R) (t_i := t_i) (t_j := t_j) :=
  IsLocalization.Away.awayToAwayRight (R := R) (x := t_j) (y := t_i)
    (P := Rij (R := R) (t_i := t_i) (t_j := t_j))

/-- The canonical map R_i to R_ij; it inverts t_j in R_i. -/
noncomputable def riToRij : Ri (R := R) (t_i := t_i) →+* Rij (R := R) (t_i := t_i) (t_j := t_j) :=
  IsLocalization.Away.awayToAwayRight (R := R) (x := t_i) (y := t_j)
    (P := Rij (R := R) (t_i := t_i) (t_j := t_j))

/-- The algebra structure of R_ij over R_j. -/
noncomputable instance rjAlgebraRij : Algebra (Rj (R := R) (t_j := t_j))
    (Rij (R := R) (t_i := t_i) (t_j := t_j)) :=
  (rjToRij (R := R) t_i t_j).toAlgebra

/-- The algebra structure of R_ij over R_i. -/
noncomputable instance riAlgebraRij : Algebra (Ri (R := R) (t_i := t_i))
    (Rij (R := R) (t_i := t_i) (t_j := t_j)) :=
  (riToRij (R := R) t_i t_j).toAlgebra

/-- The tensor-product localization instance for R_i tensor_R R_j. -/
noncomputable instance tensorLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid (Rj (R := R) (t_j := t_j))
      (Submonoid.powers t_i)) (RijTensor (R := R) (t_i := t_i) (t_j := t_j)) :=
  IsLocalization.tensorRight (R := R) (S := Rj (R := R) (t_j := t_j))
    (M := Submonoid.powers t_i) (A := Ri (R := R) (t_i := t_i))

/-- The actual tensor-product pushout square R -> R_j, R -> R_i,
R_j -> R_i tensor R_j, R_i -> R_i tensor R_j. -/
noncomputable instance tensorPushout :
    Algebra.IsPushout R (Rj (R := R) (t_j := t_j)) (Ri (R := R) (t_i := t_i))
      (RijTensor (R := R) (t_i := t_i) (t_j := t_j)) :=
  Algebra.isPushout_of_isLocalization (S := Submonoid.powers t_i)
    (T := Rj (R := R) (t_j := t_j)) (A := Ri (R := R) (t_i := t_i))
    (B := RijTensor (R := R) (t_i := t_i) (t_j := t_j))

/-- The canonical tensor localization equivalence to the product localization,
conditional on the canonical localization instance at the image of t_i in R_j. -/
noncomputable def tensorToRijEquiv
    (h : IsLocalization.Away (algebraMap R (Rj (R := R) (t_j := t_j)) t_i)
      (Rij (R := R) (t_i := t_i) (t_j := t_j))) :
    RijTensor (R := R) (t_i := t_i) (t_j := t_j) ≃ₐ[
      Rj (R := R) (t_j := t_j)] Rij (R := R) (t_i := t_i) (t_j := t_j) := by
  letI := h
  exact IsLocalization.algEquiv
    (Algebra.algebraMapSubmonoid (Rj (R := R) (t_j := t_j)) (Submonoid.powers t_i))
    (RijTensor (R := R) (t_i := t_i) (t_j := t_j))
    (Rij (R := R) (t_i := t_i) (t_j := t_j))

/-- The pushout square for the product localization R_ij, conditional on the
canonical localization instance. -/
noncomputable def awayAwayPushout
    (h : IsLocalization.Away (algebraMap R (Rj (R := R) (t_j := t_j)) t_i)
      (Rij (R := R) (t_i := t_i) (t_j := t_j))) :
    Algebra.IsPushout R (Rj (R := R) (t_j := t_j)) (Ri (R := R) (t_i := t_i))
      (Rij (R := R) (t_i := t_i) (t_j := t_j)) :=
  Algebra.IsPushout.of_equiv (tensorPushout (R := R) t_i t_j)
    (tensorToRijEquiv (R := R) t_i t_j h) (by
      ext x
      rfl)

/-- The symmetric form of the conditional pushout square. -/
noncomputable def awayAwayPushoutComm
    (h : IsLocalization.Away (algebraMap R (Rj (R := R) (t_j := t_j)) t_i)
      (Rij (R := R) (t_i := t_i) (t_j := t_j))) :
    Algebra.IsPushout R (Ri (R := R) (t_i := t_i)) (Rj (R := R) (t_j := t_j))
      (Rij (R := R) (t_i := t_i) (t_j := t_j)) :=
  Algebra.IsPushout.comm.mp (awayAwayPushout (R := R) t_i t_j h)

/-- The base-change cancellation equivalence obtained from the conditional
product pushout. -/
noncomputable def awayAwayCancel
    (h : IsLocalization.Away (algebraMap R (Rj (R := R) (t_j := t_j)) t_i)
      (Rij (R := R) (t_i := t_i) (t_j := t_j)))
    (C : Type u) [CommRing C] [Algebra R C]
    [Algebra (Rj (R := R) (t_j := t_j)) C]
    [IsScalarTower R (Rj (R := R) (t_j := t_j)) C] :
    Rij (R := R) (t_i := t_i) (t_j := t_j) ⊗[
      Ri (R := R) (t_i := t_i)] C ≃ₐ[
        Rj (R := R) (t_j := t_j)] TensorProduct R (Rj (R := R) (t_j := t_j)) C :=
  IsPushout.cancelBaseChangeAlg R (Rj (R := R) (t_j := t_j))
    (Ri (R := R) (t_i := t_i)) (Rij (R := R) (t_i := t_i) (t_j := t_j)) C

/-- The exact missing Mathlib instance: R_ij is the away localization of R_j at
the image of t_i.  This is stated explicitly because the unconditional pushout
and the reassociation ring upgrade depend on it. -/
def AwayImageLocalizationInstance : Prop :=
  IsLocalization.Away (algebraMap R (Rj (R := R) (t_j := t_j)) t_i)
    (Rij (R := R) (t_i := t_i) (t_j := t_j))

/-- The missing instance is equivalent to the conditional pushout being
available. -/
theorem awayAwayPushout_of_instance
    (h : AwayImageLocalizationInstance (R := R) (t_i := t_i) (t_j := t_j)) :
    Algebra.IsPushout R (Rj (R := R) (t_j := t_j)) (Ri (R := R) (t_i := t_i))
      (Rij (R := R) (t_i := t_i) (t_j := t_j)) :=
  awayAwayPushout (R := R) t_i t_j h

/-- The symmetric pushout from the missing instance. -/
theorem awayAwayPushoutComm_of_instance
    (h : AwayImageLocalizationInstance (R := R) (t_i := t_i) (t_j := t_j)) :
    Algebra.IsPushout R (Ri (R := R) (t_i := t_i)) (Rj (R := R) (t_j := t_j))
      (Rij (R := R) (t_i := t_i) (t_j := t_j)) :=
  awayAwayPushoutComm (R := R) t_i t_j h


namespace LeanFormal.IUT.Foundations.AwayAwayPushout

variable (R : Type u) [CommRing R] (t_i t_j : R)

/-- The canonical map R_i to the tensor-product localization. -/
noncomputable def riToTensor :
    Ri (R := R) (t_i := t_i) →+* RijTensor (R := R) (t_i := t_i) (t_j := t_j) :=
  algebraMap (Ri (R := R) (t_i := t_i))
    (RijTensor (R := R) (t_i := t_i) (t_j := t_j))

/-- The canonical map R_j to the tensor-product localization. -/
noncomputable def rjToTensor :
    Rj (R := R) (t_j := t_j) →+* RijTensor (R := R) (t_i := t_i) (t_j := t_j) :=
  algebraMap (Rj (R := R) (t_j := t_j))
    (RijTensor (R := R) (t_i := t_i) (t_j := t_j))

/-- The tensor-product pushout square commutes. -/
theorem tensorPushout_comm :
    (riToTensor (R := R) t_i t_j).comp (algebraMap R (Ri (R := R) (t_i := t_i))) =
      (rjToTensor (R := R) t_i t_j).comp (algebraMap R (Rj (R := R) (t_j := t_j))) := by
  ext x
  simp [riToTensor, rjToTensor, Algebra.algebraMap_eq_smul_one, Algebra.smul_def]

/-- The tensor localization equivalence respects the canonical R_j-algebra map,
conditional on the missing instance. -/
theorem tensorToRijEquiv_algebraMap
    (h : IsLocalization.Away (algebraMap R (Rj (R := R) (t_j := t_j)) t_i)
      (Rij (R := R) (t_i := t_i) (t_j := t_j))) (x : Rj (R := R) (t_j := t_j)) :
    tensorToRijEquiv (R := R) t_i t_j h
        (algebraMap (Rj (R := R) (t_j := t_j))
          (RijTensor (R := R) (t_i := t_i) (t_j := t_j)) x) =
      algebraMap (Rj (R := R) (t_j := t_j))
        (Rij (R := R) (t_i := t_i) (t_j := t_j)) x := by
  letI := h
  exact IsLocalization.algEquiv_apply _ _
    (algebraMap (Rj (R := R) (t_j := t_j))
      (RijTensor (R := R) (t_i := t_i) (t_j := t_j)) x)

/-- The tensor localization equivalence sends the image of t_i to the inverse
of the image, conditional on the missing instance. -/
theorem tensorToRijEquiv_isUnit_ti
    (h : IsLocalization.Away (algebraMap R (Rj (R := R) (t_j := t_j)) t_i)
      (Rij (R := R) (t_i := t_i) (t_j := t_j))) :
    IsUnit (tensorToRijEquiv (R := R) t_i t_j h
      (algebraMap (Ri (R := R) (t_i := t_i))
        (RijTensor (R := R) (t_i := t_i) (t_j := t_j)) t_i)) := by
  letI := h
  exact (IsLocalization.algEquiv _ _ _).isUnit _ (Or.inl (IsLocalization.Away.algebraMap_isUnit t_i))

/-- The conditional pushout equivalence associated to the product localization. -/
noncomputable def awayAwayPushoutEquiv
    (h : AwayImageLocalizationInstance (R := R) (t_i := t_i) (t_j := t_j)) :
    TensorProduct R (Ri (R := R) (t_i := t_i)) (Rj (R := R) (t_j := t_j)) ≃ₐ[
      Ri (R := R) (t_i := t_i)] Rij (R := R) (t_i := t_i) (t_j := t_j) :=
  (Algebra.IsPushout.equiv R (Ri (R := R) (t_i := t_i))
    (Rj (R := R) (t_j := t_j))
    (Rij (R := R) (t_i := t_i) (t_j := t_j))).trans
    (by
      letI := h
      exact IsLocalization.algEquiv
        (Algebra.algebraMapSubmonoid (Ri (R := R) (t_i := t_i)) (Submonoid.powers t_j))
        (RijTensor (R := R) (t_i := t_i) (t_j := t_j))
        (Rij (R := R) (t_i := t_i) (t_j := t_j)))

/-- The conditional product pushout has the expected tensor formula. -/
theorem awayAwayPushoutEquiv_tmul
    (h : AwayImageLocalizationInstance (R := R) (t_i := t_i) (t_j := t_j))
    (a : Ri (R := R) (t_i := t_i)) (b : Rj (R := R) (t_j := t_j)) :
    awayAwayPushoutEquiv (R := R) t_i t_j h (a ⊗ₜ b) =
      algebraMap (Ri (R := R) (t_i := t_i))
        (Rij (R := R) (t_i := t_i) (t_j := t_j)) a *
        algebraMap (Rj (R := R) (t_j := t_j))
          (Rij (R := R) (t_i := t_i) (t_j := t_j)) b := by
  letI := h
  exact Algebra.IsPushout.equiv_tmul _ _ _ _ a b

/-- The missing instance is exactly the canonical localization of R_j at the
image of t_i. -/
theorem awayImageLocalizationInstance_iff :
    AwayImageLocalizationInstance (R := R) (t_i := t_i) (t_j := t_j) ↔
      IsLocalization.Away (algebraMap R (Rj (R := R) (t_j := t_j)) t_i)
        (Rij (R := R) (t_i := t_i) (t_j := t_j)) :=
  Iff.rfl

end LeanFormal.IUT.Foundations.AwayAwayPushout

end LeanFormal.IUT.Foundations.AwayAwayPushout
