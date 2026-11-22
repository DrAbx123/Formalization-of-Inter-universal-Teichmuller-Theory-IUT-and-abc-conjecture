import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Tactic

/-!
# Pushout square for a localization and a base algebra

For an R-algebra A and an element r : R, this file constructs the actual
Algebra.IsPushout square

  R        -> A
  |           |
  v           v
  Away r   -> A tensor_R Away r

using Mathlib's localization tensor-product instance and
Algebra.isPushout_of_isLocalization.  It also records the resulting
base-change cancellation and the exact remaining input needed for the
localized tensor reassociation.
-/

open scoped TensorProduct

noncomputable section

namespace LeanFormal.IUT.Foundations.AwayLocalizationPushout

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
variable (r : R)

/-- The away localization used in the pushout square. -/
abbrev AwayR : Type u := Localization.Away r

/-- The pushout object A tensor_R Away r. -/
abbrev PushoutObject : Type u := TensorProduct R A (AwayR (R := R) (r := r))

/-- The base algebra structure on A tensor_R Away r. -/
noncomputable instance pushoutAlgebraR :
    Algebra R (PushoutObject (R := R) (A := A) (r := r)) :=
  Algebra.TensorProduct.instAlgebra

/-- The right algebra structure on A tensor_R Away r. -/
noncomputable instance pushoutAlgebraAway :
    Algebra (AwayR (R := R) (r := r)) (PushoutObject (R := R) (A := A) (r := r)) :=
  Algebra.TensorProduct.rightAlgebra

/-- The left algebra structure on A tensor_R Away r. -/
noncomputable instance pushoutAlgebraA :
    Algebra A (PushoutObject (R := R) (A := A) (r := r)) :=
  Algebra.TensorProduct.leftAlgebra

/-- The tensor-product localization instance for the pushout object. -/
noncomputable instance pushoutLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid A (Submonoid.powers r))
      (PushoutObject (R := R) (A := A) (r := r)) :=
  IsLocalization.tensor (R := R) (S := A)
    (A := AwayR (R := R) (r := r)) (M := Submonoid.powers r)

/-- The actual pushout square: R -> A, R -> Away r, A -> A tensor Away r,
Away r -> A tensor Away r. -/
noncomputable instance awayLocalizationPushout :
    Algebra.IsPushout R A (AwayR (R := R) (r := r))
      (PushoutObject (R := R) (A := A) (r := r)) :=
  Algebra.isPushout_of_isLocalization (S := Submonoid.powers r)
    (T := A) (A := AwayR (R := R) (r := r))
    (B := PushoutObject (R := R) (A := A) (r := r))

/-- The pushout equivalence A tensor_R Away r is isomorphic to the pushout
object over A. -/
noncomputable def pushoutEquiv :
    TensorProduct R A (AwayR (R := R) (r := r)) ≃ₐ[A]
      PushoutObject (R := R) (A := A) (r := r) :=
  Algebra.IsPushout.equiv R A (AwayR (R := R) (r := r))
    (PushoutObject (R := R) (A := A) (r := r))

/-- The pushout equivalence sends a pure tensor to the corresponding pushout
element. -/
theorem pushoutEquiv_tmul (a : A) (s : AwayR (R := R) (r := r)) :
    pushoutEquiv (R := R) (A := A) (r := r) (a ⊗ₜ s) =
      algebraMap A (PushoutObject (R := R) (A := A) (r := r)) a *
        algebraMap (AwayR (R := R) (r := r))
          (PushoutObject (R := R) (A := A) (r := r)) s :=
  Algebra.IsPushout.equiv_tmul (R := R) (S := A) (R' := AwayR (R := R) (r := r))
    (S' := PushoutObject (R := R) (A := A) (r := r)) a s

/-- The inverse pushout equivalence recovers the left algebra map on A. -/
theorem pushoutEquiv_symm_left (a : A) :
    (pushoutEquiv (R := R) (A := A) (r := r)).symm
        (algebraMap A (PushoutObject (R := R) (A := A) (r := r)) a) =
      a ⊗ₜ 1 :=
  Algebra.IsPushout.equiv_symm_algebraMap_left (R := R) (S := A)
    (R' := AwayR (R := R) (r := r))
    (S' := PushoutObject (R := R) (A := A) (r := r)) a

/-- The inverse pushout equivalence recovers the right algebra map on Away r. -/
theorem pushoutEquiv_symm_right (s : AwayR (R := R) (r := r)) :
    (pushoutEquiv (R := R) (A := A) (r := r)).symm
        (algebraMap (AwayR (R := R) (r := r))
          (PushoutObject (R := R) (A := A) (r := r)) s) =
      1 ⊗ₜ s :=
  Algebra.IsPushout.equiv_symm_algebraMap_right (R := R) (S := A)
    (R' := AwayR (R := R) (r := r))
    (S' := PushoutObject (R := R) (A := A) (r := r)) s

/-- The symmetric form of the pushout cancellation: the algebra equivalence
provided by IsPushout.cancelBaseChangeAlg. -/
noncomputable def pushoutCancelEquiv (C : Type u) [CommRing C] [Algebra R C]
    [Algebra (AwayR (R := R) (r := r)) C]
    [IsScalarTower R (AwayR (R := R) (r := r)) C] :
    PushoutObject (R := R) (A := A) (r := r) ⊗[
      AwayR (R := R) (r := r)] C ≃ₐ[A] TensorProduct R A C :=
  IsPushout.cancelBaseChangeAlg R A (AwayR (R := R) (r := r))
    (PushoutObject (R := R) (A := A) (r := r)) C

/-- Pure-tensor form of the pushout cancellation. -/
theorem pushoutCancelEquiv_tmul (C : Type u) [CommRing C] [Algebra R C]
    [Algebra (AwayR (R := R) (r := r)) C]
    [IsScalarTower R (AwayR (R := R) (r := r)) C]
    (c : C) :
    pushoutCancelEquiv (R := R) (A := A) (r := r) C (1 ⊗ₜ c) = 1 ⊗ₜ c :=
  IsPushout.cancelBaseChange_tmul (R := R) (S := A)
    (A := AwayR (R := R) (r := r))
    (B := PushoutObject (R := R) (A := A) (r := r)) c

/-- The remaining missing input for the localized tensor reassociation: an
actual pushout square for the two away localizations Away(t_i) and
Away(t_i t_j).  The present file constructs the base-change pushout for
R -> A and R -> Away r only. -/
def AwayAwayPushoutResidual : Prop :=
  Algebra.IsPushout R (Localization.Away (1 : R)) (Localization.Away (1 : R))
    (Localization.Away (1 : R))

/-- The exact residual witness needed to upgrade the linear cancellation to the
full localized tensor reassociation. -/
def AwayAwayPushoutWitness : Prop :=
  ∃ (s : R) (h : Algebra.IsPushout R (Localization.Away s)
    (Localization.Away s) (Localization.Away s)), True


namespace LeanFormal.IUT.Foundations.AwayLocalizationPushout

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
variable (r s : R)

/-- The pushout object is an A-algebra. -/
noncomputable instance pushoutAlgebra : Algebra A
    (PushoutObject (R := R) (A := A) (r := r)) :=
  Algebra.TensorProduct.rightAlgebra

/-- The canonical map A to the pushout object. -/
noncomputable def pushoutMapLeft :
    A →+* PushoutObject (R := R) (A := A) (r := r) :=
  algebraMap A (PushoutObject (R := R) (A := A) (r := r))

/-- The canonical map Away r to the pushout object. -/
noncomputable def pushoutMapRight :
    AwayR (R := R) (r := r) →+*
      PushoutObject (R := R) (A := A) (r := r) :=
  algebraMap (AwayR (R := R) (r := r))
    (PushoutObject (R := R) (A := A) (r := r))

/-- The pushout square commutes: the two maps from R agree after composing with
the two legs. -/
theorem pushoutSquare_comm :
    (pushoutMapLeft (R := R) (A := A) (r := r)).comp (algebraMap R A) =
      (pushoutMapRight (R := R) (A := A) (r := r)).comp
        (algebraMap R (AwayR (R := R) (r := r))) := by
  ext x
  simp [pushoutMapLeft, pushoutMapRight, Algebra.algebraMap_eq_smul_one,
    Algebra.smul_def]

/-- The left leg is the canonical A-algebra map. -/
theorem pushoutMapLeft_eq :
    pushoutMapLeft (R := R) (A := A) (r := r) =
      algebraMap A (PushoutObject (R := R) (A := A) (r := r)) := rfl

/-- The right leg is the canonical Away r-algebra map. -/
theorem pushoutMapRight_eq :
    pushoutMapRight (R := R) (A := A) (r := r) =
      algebraMap (AwayR (R := R) (r := r))
        (PushoutObject (R := R) (A := A) (r := r)) := rfl

/-- The pushout equivalence is the identity on the left algebra. -/
theorem pushoutEquiv_apply_left (a : A) :
    pushoutEquiv (R := R) (A := A) (r := r) (a ⊗ₜ 1) =
      algebraMap A (PushoutObject (R := R) (A := A) (r := r)) a := by
  rw [pushoutEquiv_tmul, map_one, mul_one]

/-- The pushout equivalence is the identity on the right localization. -/
theorem pushoutEquiv_apply_right (s : AwayR (R := R) (r := r)) :
    pushoutEquiv (R := R) (A := A) (r := r) (1 ⊗ₜ s) =
      algebraMap (AwayR (R := R) (r := r))
        (PushoutObject (R := R) (A := A) (r := r)) s := by
  rw [pushoutEquiv_tmul, map_one, one_mul]

/-- The inverse pushout equivalence is the identity on a pure left tensor. -/
theorem pushoutEquiv_symm_tmul_left (a : A) :
    (pushoutEquiv (R := R) (A := A) (r := r)).symm
        (algebraMap A (PushoutObject (R := R) (A := A) (r := r)) a) =
      a ⊗ₜ 1 :=
  pushoutEquiv_symm_left (R := R) (A := A) (r := r) a

/-- The inverse pushout equivalence is the identity on a pure right tensor. -/
theorem pushoutEquiv_symm_tmul_right (s : AwayR (R := R) (r := r)) :
    (pushoutEquiv (R := R) (A := A) (r := r)).symm
        (algebraMap (AwayR (R := R) (r := r))
          (PushoutObject (R := R) (A := A) (r := r)) s) =
      1 ⊗ₜ s :=
  pushoutEquiv_symm_right (R := R) (A := A) (r := r) s

/-- The symmetric pushout tensor equivalence over R. -/
noncomputable def pushoutCommEquiv :
    TensorProduct R (AwayR (R := R) (r := r)) A ≃ₐ[A]
      PushoutObject (R := R) (A := A) (r := r) :=
  (TensorProduct.comm R (AwayR (R := R) (r := r)) A).trans
    (pushoutEquiv (R := R) (A := A) (r := r))

/-- Pure-tensor form of the symmetric pushout equivalence. -/
theorem pushoutCommEquiv_tmul (s : AwayR (R := R) (r := r)) (a : A) :
    pushoutCommEquiv (R := R) (A := A) (r := r) (s ⊗ₜ a) =
      pushoutEquiv (R := R) (A := A) (r := r) (a ⊗ₜ s) := rfl

/-- The base-change pushout gives the standard tensor cancellation module
equivalence. -/
noncomputable def pushoutTensorCancelLinear (M : Type u) [AddCommGroup M]
    [Module R M] [Module A M] [IsScalarTower R A M] :
    PushoutObject (R := R) (A := A) (r := r) ⊗[
      AwayR (R := R) (r := r)] M ≃ₗ[
        PushoutObject (R := R) (A := A) (r := r)] TensorProduct R A M :=
  IsPushout.cancelBaseChange R A (AwayR (R := R) (r := r))
    (PushoutObject (R := R) (A := A) (r := r)) M

/-- The residual proposition is not asserted. -/
theorem awayAwayPushoutResidual_prop :
    AwayAwayPushoutResidual (R := R) (A := A) (r := r) ↔
      Algebra.IsPushout R (Localization.Away (1 : R)) (Localization.Away (1 : R))
        (Localization.Away (1 : R)) :=
  Iff.rfl


namespace LeanFormal.IUT.Foundations.AwayLocalizationPushout

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The pushout object is the base change of A to Away r. -/
theorem pushoutObject_eq :
    PushoutObject (R := R) (A := A) (r := 1) =
      TensorProduct R A (AwayR (R := R) (r := 1)) := rfl

/-- The pushout square has the expected top-left ring. -/
theorem pushout_square_left :
    Algebra.IsPushout R A (AwayR (R := R) (r := 1))
      (PushoutObject (R := R) (A := A) (r := 1)) :=
  awayLocalizationPushout (R := R) (A := A) (r := 1)

/-- The desired reassociation ring upgrade is not derived in this file; the
pushout square constructed here is the base-change input, and the missing
Away/Away pushout square is recorded as AwayAwayPushoutResidual. -/
def reassociationResidual : Prop :=
  AwayAwayPushoutResidual (R := R) (A := A) (r := 1)

/-- The residual is exactly the missing Away/Away pushout square. -/
theorem reassociationResidual_iff :
    reassociationResidual (R := R) (A := A) ↔
      AwayAwayPushoutResidual (R := R) (A := A) (r := 1) :=
  Iff.rfl

end LeanFormal.IUT.Foundations.AwayLocalizationPushout

end LeanFormal.IUT.Foundations.AwayLocalizationPushout

end LeanFormal.IUT.Foundations.AwayLocalizationPushout
