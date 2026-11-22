/- F2.1 / file2(a): `P ∤ differentIdeal ⇒ IsUnramifiedAt ⇒ ramificationIdx = 1`.

  RECON (Lead/david): `dvd_differentIdeal_iff` (Mathlib RingTheory/DedekindDomain/Different.lean;
  needs Dedekind domains + separable fraction fields),`Ideal.ramificationIdx_eq_one_iff`
  (Mathlib RingTheory/RamificationInertia/Ramification.lean:105), and david's bridge
  `Mzk1ULHbadUnramifiedDeltaActual.delta_eq_zero_of_ramificationIdx_eq_one`.
  Paper input `p ∤ relative discriminant` (Prop1.8 support classification) stays explicit
  (obligation: discharge via NumberField.not_dvd_discr_iff_isUnramifiedIn /
  natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow). No sorry/axiom. -/
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaGoodReductionActual

variable {A B : Type*} [CommRing A] [CommRing B]
  [IsDedekindDomain A] [IsDedekindDomain B] [Algebra A B]
  [Algebra (FractionRing A) (FractionRing B)]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

/-- **`P ∤ differentIdeal ⇒ IsUnramifiedAt`**。 -/
theorem isUnramifiedAt_of_not_dvd_differentIdeal (P : Ideal B) [P.IsPrime]
    (h : ¬ P ∣ differentIdeal A B) : Algebra.IsUnramifiedAt A P := by
  by_contra hunr
  exact h ((dvd_differentIdeal_iff (P := P)).mpr hunr)

/-- **`P ∤ differentIdeal ⇒ ramificationIdx = 1`**。 -/
theorem ramificationIdx_eq_one_of_not_dvd_differentIdeal [Algebra.EssFiniteType A B]
    (P : Ideal B) [P.IsPrime] (h : ¬ P ∣ differentIdeal A B) :
    P.ramificationIdx A = 1 :=
  Ideal.ramificationIdx_eq_one_iff.mpr (isUnramifiedAt_of_not_dvd_differentIdeal P h)

#print axioms isUnramifiedAt_of_not_dvd_differentIdeal
#print axioms ramificationIdx_eq_one_of_not_dvd_differentIdeal

end LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaGoodReductionActual