import LeanFormal.IUT.Foundations.AlgebraicGeometry.AwayAwayPushout
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Tactic

/-!
# The canonical image localization instance

For elements t_i t_j : R, this file proves

  IsLocalization.Away (algebraMap R (Localization.Away t_j) t_i)
    (Localization.Away (t_i * t_j)).

The proof passes through the intermediate localization

  T = Localization.Away (algebraMap R (Localization.Away t_j) t_i).

By IsLocalization.Away.mul, T is also the localization of R at t_i * t_j, hence
R-algebra equivalent to Localization.Away (t_i * t_j).  The equivalence is
upgraded to an R_j-algebra equivalence by localization extensionality, and then
the localization instance is transported across it.

No fake instance is declared; the actual instance is constructed below.
-/

open scoped TensorProduct
open AlgebraicGeometry CategoryTheory

noncomputable section

namespace LeanFormal.IUT.Foundations.AwayImageLocalizationInstance

universe u

open LeanFormal.IUT.Foundations.AwayAwayPushout

variable (R : Type u) [CommRing R] (t_i t_j : R)

/-- The localization of R_j at the image of t_i. -/
abbrev T : Type u := Localization.Away (algebraMap R (Rj (R := R) (t_j := t_j)) t_i)

/-- T is by definition the away localization of R_j at the image of t_i. -/
noncomputable instance tIsLocalizationImage :
    IsLocalization.Away (algebraMap R (Rj (R := R) (t_j := t_j)) t_i)
      (T (R := R) (t_i := t_i) (t_j := t_j)) :=
  inferInstance

/-- The algebra structure of T over R. -/
noncomputable instance tAlgebraR : Algebra R (T (R := R) (t_i := t_i) (t_j := t_j)) :=
  inferInstance

/-- The algebra structure of T over R_j. -/
noncomputable instance tAlgebraRj : Algebra (Rj (R := R) (t_j := t_j))
    (T (R := R) (t_i := t_i) (t_j := t_j)) :=
  inferInstance

/-- T is also the localization of R at the product t_i t_j. -/
noncomputable instance tIsLocalizationProduct :
    IsLocalization.Away (t_i * t_j) (T (R := R) (t_i := t_i) (t_j := t_j)) :=
  IsLocalization.Away.mul (R := R) (S := Rj (R := R) (t_j := t_j))
    (T := T (R := R) (t_i := t_i) (t_j := t_j)) t_j t_i

/-- The product localization R_ij is the away localization at t_i t_j. -/
noncomputable instance rijIsLocalizationProduct :
    IsLocalization.Away (t_i * t_j) (Rij (R := R) (t_i := t_i) (t_j := t_j)) :=
  inferInstance

/-- The R-algebra equivalence between T and R_ij, both localizations of R at
the product t_i t_j. -/
noncomputable def tRijAlgEquiv :
    T (R := R) (t_i := t_i) (t_j := t_j) ≃ₐ[R]
      Rij (R := R) (t_i := t_i) (t_j := t_j) :=
  IsLocalization.algEquiv (Submonoid.powers (t_i * t_j))
    (T (R := R) (t_i := t_i) (t_j := t_j))
    (Rij (R := R) (t_i := t_i) (t_j := t_j))

/-- The canonical R_j-algebra map from T to R_ij. -/
noncomputable def tToRijRj :
    T (R := R) (t_i := t_i) (t_j := t_j) →+*
      Rij (R := R) (t_i := t_i) (t_j := t_j) :=
  (algebraMap (Rj (R := R) (t_j := t_j))
    (Rij (R := R) (t_i := t_i) (t_j := t_j))).comp
    (algebraMap (Rj (R := R) (t_j := t_j))
      (T (R := R) (t_i := t_i) (t_j := t_j)))

/-- The R-algebra equivalence T to R_ij commutes with the R_j-algebra maps. -/
theorem tRijAlgEquiv_commutes_rj :
    (tRijAlgEquiv (R := R) t_i t_j).toRingHom.comp
        (algebraMap (Rj (R := R) (t_j := t_j))
          (T (R := R) (t_i := t_i) (t_j := t_j))) =
      algebraMap (Rj (R := R) (t_j := t_j))
        (Rij (R := R) (t_i := t_i) (t_j := t_j)) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers t_j)
  ext r
  change (tRijAlgEquiv (R := R) t_i t_j)
      (algebraMap R (T (R := R) (t_i := t_i) (t_j := t_j)) r) =
    algebraMap R (Rij (R := R) (t_i := t_i) (t_j := t_j)) r
  exact (tRijAlgEquiv (R := R) t_i t_j).commutes r

/-- The R_j-algebra equivalence between T and R_ij. -/
noncomputable def tRijAlgEquivRj :
    T (R := R) (t_i := t_i) (t_j := t_j) ≃ₐ[Rj (R := R) (t_j := t_j)]
      Rij (R := R) (t_i := t_i) (t_j := t_j) :=
  AlgEquiv.ofRingEquiv (R := Rj (R := R) (t_j := t_j))
    (f := (tRijAlgEquiv (R := R) t_i t_j).toRingEquiv)
    (by
      intro s
      exact congrArg (fun f => f s) (tRijAlgEquiv_commutes_rj (R := R) t_i t_j))

/-- The canonical image localization instance, transported across the R_j-algebra
equivalence. -/
noncomputable def awayImageLocalizationInstance :
    IsLocalization.Away (algebraMap R (Rj (R := R) (t_j := t_j)) t_i)
      (Rij (R := R) (t_i := t_i) (t_j := t_j)) :=
  IsLocalization.isLocalization_of_algEquiv
    (M := Submonoid.powers (algebraMap R (Rj (R := R) (t_j := t_j)) t_i))
    (S := T (R := R) (t_i := t_i) (t_j := t_j))
    (P := Rij (R := R) (t_i := t_i) (t_j := t_j))
    (tRijAlgEquivRj (R := R) t_i t_j)

/-- The unconditional product-localization pushout, using the constructed
instance. -/
noncomputable def awayAwayPushoutUnconditional :
    Algebra.IsPushout R (Rj (R := R) (t_j := t_j)) (Ri (R := R) (t_i := t_i))
      (Rij (R := R) (t_i := t_i) (t_j := t_j)) :=
  awayAwayPushout (R := R) t_i t_j (awayImageLocalizationInstance (R := R) t_i t_j)

/-- The unconditional symmetric pushout. -/
noncomputable def awayAwayPushoutCommUnconditional :
    Algebra.IsPushout R (Ri (R := R) (t_i := t_i)) (Rj (R := R) (t_j := t_j))
      (Rij (R := R) (t_i := t_i) (t_j := t_j)) :=
  Algebra.IsPushout.comm.mp (awayAwayPushoutUnconditional (R := R) t_i t_j)

/-- The missing instance residual is closed by the actual construction. -/
theorem awayImageLocalizationInstance_closes_residual :
    AwayImageLocalizationInstance (R := R) (t_i := t_i) (t_j := t_j) :=
  awayImageLocalizationInstance (R := R) t_i t_j

/-- The image-localization equivalence sends the image of t_j to the product
localization in the expected way. -/
theorem tRijAlgEquiv_tmul_formula
    (x : Rj (R := R) (t_j := t_j)) :
    tRijAlgEquivRj (R := R) t_i t_j
        (algebraMap (Rj (R := R) (t_j := t_j))
          (T (R := R) (t_i := t_i) (t_j := t_j)) x) =
      algebraMap (Rj (R := R) (t_j := t_j))
        (Rij (R := R) (t_i := t_i) (t_j := t_j)) x := by
  exact AlgEquiv.commutes (tRijAlgEquivRj (R := R) t_i t_j) x

/-- The constructed instance is the canonical product localization. -/
theorem awayImageLocalizationInstance_spec :
    IsLocalization.Away (algebraMap R (Rj (R := R) (t_j := t_j)) t_i)
      (Rij (R := R) (t_i := t_i) (t_j := t_j)) :=
  awayImageLocalizationInstance (R := R) t_i t_j


namespace LeanFormal.IUT.Foundations.AwayImageLocalizationInstance

variable (R : Type u) [CommRing R] (t_i t_j : R)

/-- The R_j-algebra equivalence T to R_ij has the expected source algebra map. -/
theorem tRijAlgEquivRj_algebraMap (x : Rj (R := R) (t_j := t_j)) :
    tRijAlgEquivRj (R := R) t_i t_j
        (algebraMap (Rj (R := R) (t_j := t_j))
          (T (R := R) (t_i := t_i) (t_j := t_j)) x) =
      algebraMap (Rj (R := R) (t_j := t_j))
        (Rij (R := R) (t_i := t_i) (t_j := t_j)) x :=
  AlgEquiv.commutes (tRijAlgEquivRj (R := R) t_i t_j) x

/-- The inverse R_j-algebra equivalence recovers the R_j image. -/
theorem tRijAlgEquivRj_symm_algebraMap (x : Rj (R := R) (t_j := t_j)) :
    (tRijAlgEquivRj (R := R) t_i t_j).symm
        (algebraMap (Rj (R := R) (t_j := t_j))
          (Rij (R := R) (t_i := t_i) (t_j := t_j)) x) =
      algebraMap (Rj (R := R) (t_j := t_j))
        (T (R := R) (t_i := t_i) (t_j := t_j)) x := by
  rw [← tRijAlgEquivRj_algebraMap (R := R) t_i t_j x]
  exact AlgEquiv.symm_apply_apply (tRijAlgEquivRj (R := R) t_i t_j) _

/-- The canonical R_j-algebra map T to R_ij factors through the equivalence. -/
theorem tToRijRj_eq :
    tToRijRj (R := R) t_i t_j =
      (tRijAlgEquivRj (R := R) t_i t_j).toRingHom.comp
        (algebraMap (Rj (R := R) (t_j := t_j))
          (T (R := R) (t_i := t_i) (t_j := t_j))) := by
  ext x
  exact (tRijAlgEquivRj_algebraMap (R := R) t_i t_j x).symm

/-- The transported localization instance has the expected unit property. -/
theorem awayImageLocalizationInstance_isUnit :
    IsUnit (algebraMap R (Rij (R := R) (t_i := t_i) (t_j := t_j))
      (algebraMap R (Rj (R := R) (t_j := t_j)) t_i)) :=
  IsLocalization.Away.algebraMap_isUnit (R := R)
    (S := Rij (R := R) (t_i := t_i) (t_j := t_j))
    (t_i * t_j)

/-- The unconditional base-change cancellation from the constructed pushout. -/
noncomputable def awayAwayCancelUnconditional (C : Type u) [CommRing C] [Algebra R C]
    [Algebra (Rj (R := R) (t_j := t_j)) C]
    [IsScalarTower R (Rj (R := R) (t_j := t_j)) C] :
    Rij (R := R) (t_i := t_i) (t_j := t_j) ⊗[
      Ri (R := R) (t_i := t_i)] C ≃ₐ[
        Rj (R := R) (t_j := t_j)] TensorProduct R (Rj (R := R) (t_j := t_j)) C :=
  IsPushout.cancelBaseChangeAlg R (Rj (R := R) (t_j := t_j))
    (Ri (R := R) (t_i := t_i)) (Rij (R := R) (t_i := t_i) (t_j := t_j)) C

/-- The unconditional pushout and cancellation package the product localization
reassociation input. -/
theorem awayAwayPushoutUnconditional_spec :
    Algebra.IsPushout R (Rj (R := R) (t_j := t_j)) (Ri (R := R) (t_i := t_i))
      (Rij (R := R) (t_i := t_i) (t_j := t_j)) :=
  awayAwayPushoutUnconditional (R := R) t_i t_j

/-- The symmetric pushout is available unconditionally. -/
theorem awayAwayPushoutCommUnconditional_spec :
    Algebra.IsPushout R (Ri (R := R) (t_i := t_i)) (Rj (R := R) (t_j := t_j))
      (Rij (R := R) (t_i := t_i) (t_j := t_j)) :=
  awayAwayPushoutCommUnconditional (R := R) t_i t_j

end LeanFormal.IUT.Foundations.AwayImageLocalizationInstance

end LeanFormal.IUT.Foundations.AwayImageLocalizationInstance
