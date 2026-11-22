import LeanFormal.IUT.IUTII.Theta.UnitGeneratedMonoidComparison
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

/-!
# Theta-link algebraic assembly

This file builds the algebraic core of the Theta-link from the actual
unit-generated monoid comparison already proved in
`UnitGeneratedMonoidComparison`.

The construction is deliberately parameterized by two ambient commutative
groups, two independently embedded unit groups, two distinguished generators
`qbar` and `Theta`, and two nonzero integer degree maps.  The resulting link

  `u * qbar^n  |->  e(u) * Theta^n`

is an actual multiplicative equivalence of the generated submonoids, with
unique representation, generator/unit laws and naturality inherited from the
comparison theorem.

The file also constructs the evaluated-orbit synchronization used in the
Theta-link: for a label `j`, the source orbit is the set of unit multiples of
`qbar^(j^2)`, and the target orbit is the corresponding set of unit multiples
of `Theta^(j^2)`.  The link maps the first orbit onto the second whenever the
unit equivalence carries the chosen root-of-unity subgroup to the target one.
This is the algebraic content of the `mu_(2l)` ambiguity; it does not assert
that the source geometric theta divisor or tempered fundamental group has been
identified.
-/

namespace LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly

open LeanFormal.IUT.IUTII.Theta.UnitGeneratedMonoidComparison
open Multiplicative

section Core

variable {U V G H : Type*} [Group U] [Group V] [CommGroup G] [CommGroup H]
variable (u : U →* G) (v : V →* H) (q : G) (theta : H)
variable (degreeG : G →* Multiplicative ℤ) (degreeH : H →* Multiplicative ℤ)
variable (hu : Function.Injective u) (hv : Function.Injective v)
variable (hunitG : ∀ a, degreeG (u a) = 1)
variable (hunitH : ∀ b, degreeH (v b) = 1)
variable (hq : (degreeG q).toAdd ≠ 0)
variable (htheta : (degreeH theta).toAdd ≠ 0)

/-- The Theta-link on the actual unit-generated submonoids.  The unit
equivalence is the only extra input; the generator exponent is preserved. -/
noncomputable def thetaLink (e : U ≃* V) :
    unitGeneratedSubmonoid u q ≃* unitGeneratedSubmonoid v theta :=
  comparisonEquiv u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e

/-- The defining formula of the Theta-link on a unit-power expression. -/
@[simp]
theorem thetaLink_unitPower (e : U ≃* V) (a : U) (n : ℕ) :
    thetaLink u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e
        (unitPowerElement u q a n) =
      unitPowerElement v theta (e a) n :=
  comparisonEquiv_unitPower u v q theta degreeG degreeH hu hv hunitG hunitH
    hq htheta e a n

/-- The Theta-link sends the source unit subgroup to the target unit subgroup. -/
@[simp]
theorem thetaLink_embeddedUnit (e : U ≃* V) (a : U) :
    thetaLink u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e
        (embeddedUnit u q a) = embeddedUnit v theta (e a) :=
  comparisonEquiv_embeddedUnit u v q theta degreeG degreeH hu hv hunitG hunitH
    hq htheta e a

/-- The Theta-link sends `qbar` to `Theta`. -/
@[simp]
theorem thetaLink_generator (e : U ≃* V) :
    thetaLink u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e
        (distinguishedGenerator u q) = distinguishedGenerator v theta :=
  comparisonEquiv_generator u v q theta degreeG degreeH hu hv hunitG hunitH
    hq htheta e

/-- The inverse Theta-link, for the reverse comparison. -/
noncomputable def thetaLinkSymm (e : U ≃* V) :
    unitGeneratedSubmonoid v theta ≃* unitGeneratedSubmonoid u q :=
  (thetaLink u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e).symm

@[simp]
theorem thetaLinkSymm_apply (e : U ≃* V)
    (x : unitGeneratedSubmonoid v theta) :
    thetaLinkSymm u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e x =
      (thetaLink u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e).symm x :=
  rfl

include degreeG hu hunitG hq in
/-- Unique representation in the source monoid, exposed for the Theta-link
consumer. -/
theorem thetaLink_source_representation (x : unitGeneratedSubmonoid u q) :
    ∃! r : U × ℕ, (x : G) = u r.1 * q ^ r.2 :=
  existsUnique_unitPower u q degreeG hu hunitG hq x

include degreeH hv hunitH htheta in
/-- Unique representation in the target monoid. -/
theorem thetaLink_target_representation (y : unitGeneratedSubmonoid v theta) :
    ∃! r : V × ℕ, (y : H) = v r.1 * theta ^ r.2 :=
  existsUnique_unitPower v theta degreeH hv hunitH htheta y

/-- Universal property: any monoid homomorphism between the generated
submonoids that agrees with the unit equivalence on units and sends the
distinguished generator to the distinguished generator is the Theta-link. -/
theorem thetaLink_unique (e : U ≃* V)
    (f : unitGeneratedSubmonoid u q →* unitGeneratedSubmonoid v theta)
    (hunit : ∀ a : U, f (embeddedUnit u q a) = embeddedUnit v theta (e a))
    (hgen : f (distinguishedGenerator u q) = distinguishedGenerator v theta) :
    f = thetaLink u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e := by
  ext x
  obtain ⟨a, n, hx⟩ := x.property
  have hx' : x = unitPowerElement u q a n := Subtype.ext hx
  rw [hx', unitPowerElement_eq]
  simp [hunit, hgen]

/-- The Theta-link determines the unit equivalence: two unit equivalences
inducing the same link are equal. -/
theorem thetaLink_unitEquiv_ext (e₁ e₂ : U ≃* V)
    (h : ∀ x : unitGeneratedSubmonoid u q,
      thetaLink u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e₁ x =
        thetaLink u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e₂ x) :
    e₁ = e₂ := by
  ext a
  have hlink : embeddedUnit v theta (e₁ a) = embeddedUnit v theta (e₂ a) := by
    simpa only [thetaLink_embeddedUnit] using h (embeddedUnit u q a)
  apply hv
  simpa [embeddedUnit] using congrArg (fun z : unitGeneratedSubmonoid v theta => (z : H)) hlink

end Core

section EvaluationOrbits

variable {U V G H : Type*} [Group U] [Group V] [CommGroup G] [CommGroup H]
variable (u : U →* G) (v : V →* H) (q : G) (theta : H)
variable (degreeG : G →* Multiplicative ℤ) (degreeH : H →* Multiplicative ℤ)
variable (hu : Function.Injective u) (hv : Function.Injective v)
variable (hunitG : ∀ a, degreeG (u a) = 1)
variable (hunitH : ∀ b, degreeH (v b) = 1)
variable (hq : (degreeG q).toAdd ≠ 0)
variable (htheta : (degreeH theta).toAdd ≠ 0)

/-- The evaluated source orbit at exponent `n`: all unit multiples of
`qbar^n`.  This is the algebraic form of the source's
`mu_(2l) * qbar^(j^2)` orbit. -/
def sourceEvaluationOrbit (mu : Subgroup U) (n : ℕ) :
    Set (unitGeneratedSubmonoid u q) :=
  {x | ∃ zeta : U, zeta ∈ mu ∧ x = unitPowerElement u q zeta n}

/-- The evaluated target orbit at exponent `n`: all unit multiples of
`Theta^n`. -/
def targetEvaluationOrbit (nu : Subgroup V) (n : ℕ) :
    Set (unitGeneratedSubmonoid v theta) :=
  {y | ∃ zeta : V, zeta ∈ nu ∧ y = unitPowerElement v theta zeta n}

/-- The squared-label orbit `mu * qbar^(j^2)`. -/
def sourceSquaredLabelOrbit (mu : Subgroup U) (j : ℤ) :
    Set (unitGeneratedSubmonoid u q) :=
  sourceEvaluationOrbit u q mu (Int.toNat (j * j))

/-- The squared-label orbit `nu * Theta^(j^2)`. -/
def targetSquaredLabelOrbit (nu : Subgroup V) (j : ℤ) :
    Set (unitGeneratedSubmonoid v theta) :=
  targetEvaluationOrbit v theta nu (Int.toNat (j * j))

/-- The unit equivalence carries the chosen root-of-unity subgroup onto the
target root-of-unity subgroup. -/
def CarriesRootSubgroup (e : U ≃* V) (mu : Subgroup U) (nu : Subgroup V) : Prop :=
  ∀ zeta : U, zeta ∈ mu ↔ e zeta ∈ nu

/-- Orbit synchronization: the Theta-link maps every source evaluated orbit
onto the target evaluated orbit at the same exponent. -/
theorem thetaLink_image_sourceEvaluationOrbit (e : U ≃* V)
    (mu : Subgroup U) (nu : Subgroup V) (he : CarriesRootSubgroup e mu nu)
    (n : ℕ) :
    thetaLink u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e ''
        sourceEvaluationOrbit u q mu n =
      targetEvaluationOrbit v theta nu n := by
  ext y
  constructor
  · rintro ⟨x, ⟨zeta, hzeta, rfl⟩, rfl⟩
    exact ⟨e zeta, (he zeta).mp hzeta, by
      simp [thetaLink_unitPower]⟩
  · rintro ⟨zeta, hzeta, rfl⟩
    refine ⟨unitPowerElement u q (e.symm zeta) n, ?_, ?_⟩
    · exact ⟨e.symm zeta, (he (e.symm zeta)).mpr (by simpa using hzeta), rfl⟩
    · simp [thetaLink_unitPower]

/-- The squared-label specialization of orbit synchronization, matching the
source's `mu_(2l) * qbar^(j^2)` evaluation orbit. -/
theorem thetaLink_image_sourceSquaredLabelOrbit (e : U ≃* V)
    (mu : Subgroup U) (nu : Subgroup V) (he : CarriesRootSubgroup e mu nu)
    (j : ℤ) :
    thetaLink u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e ''
        sourceSquaredLabelOrbit u q mu j =
      targetSquaredLabelOrbit v theta nu j :=
  thetaLink_image_sourceEvaluationOrbit u v q theta degreeG degreeH hu hv
    hunitG hunitH hq htheta e mu nu he (Int.toNat (j * j))

/-- A common label family with a unit-root compatibility gives synchronized
evaluation orbits on both sides.  This packages the `j`-indexed family without
choosing a common root for different labels. -/
theorem thetaLink_synchronized_evaluation
    (e : U ≃* V) (mu : Subgroup U) (nu : Subgroup V)
    (he : CarriesRootSubgroup e mu nu) (J : Type*) (label : J → ℤ) :
    ∀ j : J,
      thetaLink u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e ''
          sourceSquaredLabelOrbit u q mu (label j) =
        targetSquaredLabelOrbit v theta nu (label j) :=
  fun j => thetaLink_image_sourceSquaredLabelOrbit u v q theta degreeG degreeH
    hu hv hunitG hunitH hq htheta e mu nu he (label j)

end EvaluationOrbits

section Naturality

variable {U V G H U' V' G' H' : Type*}
variable [Group U] [Group V] [CommGroup G] [CommGroup H]
variable [Group U'] [Group V'] [CommGroup G'] [CommGroup H']

/-- Naturality of the Theta-link under compatible ambient and unit maps.  This
is the Theta-link specialization of the full naturality square proved for the
unit-generated monoid comparison. -/
theorem thetaLink_natural
    (u : U →* G) (v : V →* H) (q : G) (theta : H)
    (degreeG : G →* Multiplicative ℤ) (degreeH : H →* Multiplicative ℤ)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (hunitG : ∀ a, degreeG (u a) = 1) (hunitH : ∀ b, degreeH (v b) = 1)
    (hq : (degreeG q).toAdd ≠ 0) (htheta : (degreeH theta).toAdd ≠ 0)
    (u' : U' →* G') (v' : V' →* H') (q' : G') (theta' : H')
    (degreeG' : G' →* Multiplicative ℤ) (degreeH' : H' →* Multiplicative ℤ)
    (hu' : Function.Injective u') (hv' : Function.Injective v')
    (hunitG' : ∀ a, degreeG' (u' a) = 1)
    (hunitH' : ∀ b, degreeH' (v' b) = 1)
    (hq' : (degreeG' q').toAdd ≠ 0) (htheta' : (degreeH' theta').toAdd ≠ 0)
    (e : U ≃* V) (e' : U' ≃* V')
    (ambientG : G →* G') (ambientH : H →* H')
    (unitsU : U →* U') (unitsV : V →* V')
    (hunitsG : ∀ a, ambientG (u a) = u' (unitsU a))
    (hunitsH : ∀ b, ambientH (v b) = v' (unitsV b))
    (hgeneratorG : ambientG q = q') (hgeneratorH : ambientH theta = theta')
    (hcompat : ∀ a, unitsV (e a) = e' (unitsU a))
    (x : unitGeneratedSubmonoid u q) :
    inducedMonoidMap v v' theta theta' ambientH unitsV hunitsH hgeneratorH
        (thetaLink u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e x) =
      thetaLink u' v' q' theta' degreeG' degreeH' hu' hv' hunitG' hunitH'
        hq' htheta' e'
        (inducedMonoidMap u u' q q' ambientG unitsU hunitsG hgeneratorG x) :=
  comparisonEquiv_natural u v q theta degreeG degreeH hu hv hunitG hunitH
    hq htheta u' v' q' theta' degreeG' degreeH' hu' hv' hunitG' hunitH'
    hq' htheta' e e' ambientG ambientH unitsU unitsV hunitsG hunitsH
    hgeneratorG hgeneratorH hcompat x

end Naturality

end LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly
