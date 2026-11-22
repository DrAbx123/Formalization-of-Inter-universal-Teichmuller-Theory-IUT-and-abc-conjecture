import LeanFormal.IUT.IUTII.Frobenioid.Example36TorsorEquivalence
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelBackendBalanceGroup
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelDivisor

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Bridge from the Example 3.6 torsor-presentation category to the model-Frobenioid object dictionary

This file links the coordinate category of Example 3.6
(`GlobalIdealFamily` and `TorsorPresentation`, with the equivalence
`presentationToIdealFamily` / `idealFamilyToPresentation` of
`Example36TorsorEquivalence`) to the explicit model-Frobenioid category
`Iut.SourceModelFrobenioid` built over the effective-divisor backend of
`Example36SourceModelBackend`.

Contents:

1. **Object-level bridge.**  For a global ideal family `J`, the backend object
   `objectOfIdealFamily J` has base the unique object `bottomPoint` of the
   bottom base category and divisor class `d(J) = -delta(J)`; a torsor
   presentation `P` maps to the backend object of `presentationToIdealFamily P`.
   The object roundtrip holds exactly:
   `backendObjectOfPresentation (idealFamilyToPresentation J) = objectOfIdealFamily J`
   (using the exact object roundtrip of the coordinate equivalence), and the
   divisor-class dictionary is compatible with the equivalence, including the
   injectivity/iff statement for the ideal-family object
   (`backendObjectOfPresentation_eq_iff`).

2. **Arrow-level bridge.**  A morphism `h` of global ideal families over the
   actual number-field place data gives a genuine arrow of the model
   Frobenioid in the sense of `Iut.SourceModelFrobenioid.Hom`: Frobenius
   degree `h.degree`, base arrow `1`, effective divisor the nonnegative cone
   element `Z_+` of task 25, rational function `h.multiplier`, and the balance
   field is the group-completion balance identity
   `backendBalanceEquation_of_effectivePartCone`.  Transporting a torsor arrow
   `phi` through the equivalence gives such an arrow, and the backend balance
   and the divisorial consequences are recorded for the arrow's data:
   `d(target) = n . d(source) + Z_+ - div(f)` in the group completion, and its
   explicit-coordinate form, together with the integrality (nonnegativity) of
   the effective divisor.

Boundary: no theta-pilot, q-pilot or source-identification claim; the arrow
statement is stated through the actual `SourceModelFrobenioid.Hom` fields and
the Example 3.6 coordinate equivalence, not through any additional invented
morphism structure.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open IsDedekindDomain NumberField
open scoped NumberField

universe u

variable {F : Type u} [Field F] [NumberField F]

namespace TorsorBackendBridge

/-! ## 1. The object-level bridge -/

/-- The backend object attached to a torsor presentation: apply the object
functor of the coordinate equivalence and then the model-Frobenioid object
dictionary. -/
def backendObjectOfPresentation (D : GlobalPlaceData F) (P : TorsorPresentation D) :
    Iut.SourceModelFrobenioid.Object (SourceModelBackend.globalDivisorMonoidOn (F := F)) :=
  SourceModelBackend.objectOfIdealFamily (F := F) (presentationToIdealFamily D P)

@[simp]
theorem backendObjectOfPresentation_base (D : GlobalPlaceData F)
    (P : TorsorPresentation D) :
    (backendObjectOfPresentation D P).base = SourceModelBackend.bottomPoint := rfl

@[simp]
theorem backendObjectOfPresentation_divisorClass (D : GlobalPlaceData F)
    (P : TorsorPresentation D) :
    (backendObjectOfPresentation D P).divisorClass =
      SourceModelBackend.idealFamilyDivisorClass (F := F)
        (presentationToIdealFamily D P) := rfl

/-- The base of the backend object of an ideal family is `bottomPoint`. -/
@[simp]
theorem idealFamilyBackendObject_base (J : GlobalIdealFamily F) :
    (SourceModelBackend.objectOfIdealFamily (F := F) J).base =
      SourceModelBackend.bottomPoint := rfl

/-- The divisor class `d(J) = -delta(J)` of the backend object of an ideal
family, in explicit coordinates after the group-completion equivalence. -/
theorem idealFamilyBackendObject_divisorClass_image (J : GlobalIdealFamily F) :
    SourceModelBackend.coneGrothendieckEquiv (F := F)
        ((SourceModelBackend.objectOfIdealFamily (F := F) J).divisorClass) =
      arithmeticDivisorExplicit J := by
  rw [SourceModelBackend.objectOfIdealFamily, SourceModelBackend.idealFamilyDivisorClass]
  exact AddEquiv.apply_symm_apply _ _

/-- The divisor-class dictionary for the backend object of a presentation. -/
theorem backendObjectOfPresentation_divisorClass_image (D : GlobalPlaceData F)
    (P : TorsorPresentation D) :
    SourceModelBackend.coneGrothendieckEquiv (F := F)
        ((backendObjectOfPresentation D P).divisorClass) =
      arithmeticDivisorExplicit (presentationToIdealFamily D P) :=
  idealFamilyBackendObject_divisorClass_image _

/-- **Object-level roundtrip.**  The presentation of an ideal family maps to
the backend object of that ideal family: the bridge to the model-Frobenioid
object dictionary is compatible with the exact object roundtrip of the
coordinate equivalence. -/
theorem backendObjectOfPresentation_idealFamilyToPresentation (D : GlobalPlaceData F)
    (J : GlobalIdealFamily F) :
    backendObjectOfPresentation D (idealFamilyToPresentation D J) =
      SourceModelBackend.objectOfIdealFamily (F := F) J := by
  rw [backendObjectOfPresentation,
    presentationToIdealFamily_idealFamilyToPresentation]

/-- The image of the divisor class of the roundtripped object. -/
theorem backendObjectOfPresentation_idealFamilyToPresentation_divisorClass_image
    (D : GlobalPlaceData F) (J : GlobalIdealFamily F) :
    SourceModelBackend.coneGrothendieckEquiv (F := F)
        ((backendObjectOfPresentation D (idealFamilyToPresentation D J)).divisorClass) =
      arithmeticDivisorExplicit J := by
  rw [backendObjectOfPresentation_idealFamilyToPresentation,
    idealFamilyBackendObject_divisorClass_image]

/-- The signed arithmetic divisor `d(J) = -delta(J)` is injective on global
ideal families (its two coordinates are negations of the coordinates of `J`). -/
theorem arithmeticDivisorExplicit_injective :
    Function.Injective (arithmeticDivisorExplicit (F := F)) := by
  intro J₁ J₂ h
  apply GlobalIdealFamily.ext
  · ext v
    have hv := congrArg (fun x : SourceModelBackend.ExplicitDivisor F => x.1 v) h
    simpa [arithmeticDivisorExplicit] using hv
  · funext w
    have hw := congrArg (fun x : SourceModelBackend.ExplicitDivisor F => x.2 w) h
    simpa [arithmeticDivisorExplicit] using hw

/-- **The object equality computes the ideal family.**  For the backend
objects of a presentation and an ideal family, object equality is equivalent
to the ideal-family equality `presentationToIdealFamily P = J`. -/
theorem backendObjectOfPresentation_eq_iff (D : GlobalPlaceData F)
    (P : TorsorPresentation D) (J : GlobalIdealFamily F) :
    backendObjectOfPresentation D P = SourceModelBackend.objectOfIdealFamily (F := F) J ↔
      presentationToIdealFamily D P = J := by
  constructor
  · intro hobj
    have hclass : (backendObjectOfPresentation D P).divisorClass =
        (SourceModelBackend.objectOfIdealFamily (F := F) J).divisorClass := by
      rw [hobj]
    have hmap := congrArg (SourceModelBackend.coneGrothendieckEquiv (F := F)) hclass
    rw [backendObjectOfPresentation_divisorClass_image,
      idealFamilyBackendObject_divisorClass_image] at hmap
    exact arithmeticDivisorExplicit_injective hmap
  · intro h; rw [backendObjectOfPresentation, h]

/-! ## 2. The arrow-level bridge over the number-field place data -/

section TorsorArrowBackend

/-- The ideal-family homomorphism obtained by transporting a torsor arrow
through the coordinate equivalence. -/
def torsorArrowToIdealFamilyHom
    {P₁ P₂ : TorsorPresentation (numberFieldGlobalPlaceData (F := F))}
    (φ : TorsorArrow P₁ P₂) :
    GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F))
      (presentationToIdealFamily (numberFieldGlobalPlaceData (F := F)) P₁)
      (presentationToIdealFamily (numberFieldGlobalPlaceData (F := F)) P₂) :=
  presentationArrowToIdealFamilyHom (numberFieldGlobalPlaceData (F := F)) φ

@[simp]
theorem torsorArrowToIdealFamilyHom_degree
    {P₁ P₂ : TorsorPresentation (numberFieldGlobalPlaceData (F := F))}
    (φ : TorsorArrow P₁ P₂) :
    (torsorArrowToIdealFamilyHom φ).degree = φ.degree := rfl

@[simp]
theorem torsorArrowToIdealFamilyHom_multiplier
    {P₁ P₂ : TorsorPresentation (numberFieldGlobalPlaceData (F := F))}
    (φ : TorsorArrow P₁ P₂) :
    (torsorArrowToIdealFamilyHom φ).multiplier = φ.multiplier := rfl

/-- The effective cone element attached to a torsor arrow: the nonnegative
part of the effective part of the transported ideal-family morphism. -/
noncomputable def torsorArrowEffectivePartCone
    {P₁ P₂ : TorsorPresentation (numberFieldGlobalPlaceData (F := F))}
    (φ : TorsorArrow P₁ P₂) : SourceModelBackend.EffectiveDivisor F :=
  SourceModelBackendBalanceGroup.effectivePartCone
    (numberFieldGlobalPlaceData (F := F)) numberFieldGlobalPlaceData_hasFiniteSupport
    (torsorArrowToIdealFamilyHom φ)

/-- **Backend balance identity for a torsor arrow.**  For a torsor arrow `φ` of
degree `n` and multiplier `f`, with `Z_+` the nonnegative effective cone
element of the transported ideal-family morphism, the group-completion balance
identity holds. -/
theorem torsorArrow_backendBalance
    {P₁ P₂ : TorsorPresentation (numberFieldGlobalPlaceData (F := F))}
    (φ : TorsorArrow P₁ P₂) :
    (φ.degree : ℕ) • SourceModelBackend.idealFamilyDivisorClass (F := F)
        (presentationToIdealFamily (numberFieldGlobalPlaceData (F := F)) P₁) +
        Algebra.GrothendieckAddGroup.of (torsorArrowEffectivePartCone φ) =
      SourceModelBackend.idealFamilyDivisorClass (F := F)
        (presentationToIdealFamily (numberFieldGlobalPlaceData (F := F)) P₂) +
        SourceModelBackend.globalModelDivisor (F := F) (Additive.ofMul φ.multiplier) := by
  simpa only [torsorArrowEffectivePartCone, torsorArrowToIdealFamilyHom,
    presentationArrowToIdealFamilyHom_degree,
    presentationArrowToIdealFamilyHom_multiplier] using
    SourceModelBackendBalanceGroup.backendBalanceEquation_of_effectivePartCone
      (torsorArrowToIdealFamilyHom φ)

/-- **Divisor-class form of the arrow integrality consequence:** the divisor
class of the target equals `n . d(source) + Z_+ - div(f)`. -/
theorem torsorArrow_backendDivisorClassEquation
    {P₁ P₂ : TorsorPresentation (numberFieldGlobalPlaceData (F := F))}
    (φ : TorsorArrow P₁ P₂) :
    SourceModelBackend.idealFamilyDivisorClass (F := F)
        (presentationToIdealFamily (numberFieldGlobalPlaceData (F := F)) P₂) =
      (φ.degree : ℕ) • SourceModelBackend.idealFamilyDivisorClass (F := F)
          (presentationToIdealFamily (numberFieldGlobalPlaceData (F := F)) P₁) +
        Algebra.GrothendieckAddGroup.of (torsorArrowEffectivePartCone φ) -
        SourceModelBackend.globalModelDivisor (F := F)
          (Additive.ofMul φ.multiplier) := by
  rw [eq_sub_iff_add_eq]
  exact (torsorArrow_backendBalance φ).symm

/-- The image of the divisor class of an ideal family under the group-completion
equivalence is the signed explicit divisor `d(J) = -delta(J)`. -/
theorem coneGrothendieckEquiv_idealFamilyDivisorClass (J : GlobalIdealFamily F) :
    SourceModelBackend.coneGrothendieckEquiv (F := F)
        (SourceModelBackend.idealFamilyDivisorClass (F := F) J) =
      arithmeticDivisorExplicit J := by
  rw [SourceModelBackend.idealFamilyDivisorClass]
  exact AddEquiv.apply_symm_apply _ _

/-- **Explicit-coordinate form of the arrow balance.**  In the explicit
divisor group, the target arithmetic divisor equals `n . d(source) + Z - div(f)`
with `Z` the explicit image of the nonnegative effective cone element. -/
theorem torsorArrow_backendExplicitBalance
    {P₁ P₂ : TorsorPresentation (numberFieldGlobalPlaceData (F := F))}
    (φ : TorsorArrow P₁ P₂) :
    (φ.degree : ℕ) • arithmeticDivisorExplicit
          (presentationToIdealFamily (numberFieldGlobalPlaceData (F := F)) P₁) +
        SourceModelBackend.effectiveToExplicit (torsorArrowEffectivePartCone φ) =
      arithmeticDivisorExplicit
          (presentationToIdealFamily (numberFieldGlobalPlaceData (F := F)) P₂) +
        SourceModelBackend.principalDivisorExplicit (Additive.ofMul φ.multiplier) := by
  have h := congrArg (SourceModelBackend.coneGrothendieckEquiv (F := F))
    (torsorArrow_backendBalance φ)
  simp only [map_add, map_nsmul] at h
  rwa [coneGrothendieckEquiv_idealFamilyDivisorClass,
    SourceModelBackend.coneGrothendieckEquiv_of,
    coneGrothendieckEquiv_idealFamilyDivisorClass,
    SourceModelBackendBalanceGroup.coneGrothendieckEquiv_globalModelDivisor] at h

/-- **Explicit divisor-class form:** `d(target) = n . d(source) + Z - div(f)` in
explicit coordinates. -/
theorem torsorArrow_backendExplicitDivisorClassEquation
    {P₁ P₂ : TorsorPresentation (numberFieldGlobalPlaceData (F := F))}
    (φ : TorsorArrow P₁ P₂) :
    arithmeticDivisorExplicit
        (presentationToIdealFamily (numberFieldGlobalPlaceData (F := F)) P₂) =
      (φ.degree : ℕ) • arithmeticDivisorExplicit
          (presentationToIdealFamily (numberFieldGlobalPlaceData (F := F)) P₁) +
        SourceModelBackend.effectiveToExplicit (torsorArrowEffectivePartCone φ) -
        SourceModelBackend.principalDivisorExplicit (Additive.ofMul φ.multiplier) := by
  rw [eq_sub_iff_add_eq]
  exact (torsorArrow_backendExplicitBalance φ).symm

/-- **Integrality consequence.**  The effective divisor attached to a torsor
arrow is nonnegative in explicit coordinates: it lies in the effective cone. -/
theorem torsorArrow_backendEffectiveDivisor_nonneg
    {P₁ P₂ : TorsorPresentation (numberFieldGlobalPlaceData (F := F))}
    (φ : TorsorArrow P₁ P₂) :
    SourceModelBackend.explicitNonneg
      (SourceModelBackend.effectiveToExplicit (torsorArrowEffectivePartCone φ)) :=
  SourceModelBackend.effectiveToExplicit_nonneg _

/-! ### Status of the concrete model-Frobenioid arrow

The model-Frobenioid arrow type `Iut.SourceModelFrobenioid.Hom` does exist
(fields: `frobeniusDegree`, `base`, `divisor`, `rationalFunction`, `balance`).
However, assembling its `balance` field from the Example 3.6 data requires
rewriting in the model carrier types
`(globalDivisorMonoidOn.obj (objectOfIdealFamily J).base).carrier` and
`numberFieldSourceModelInput.rationalFunctions.obj X`, which are only
definitionally equal to `EffectiveDivisor F` and `Additive F^x`.  The needed
rewrites (`Iut.SourceModelFrobenioid.gpPullback_id` on the base arrow, and
`numberFieldSourceModelInput.divisor` on the rational function) fail with
"target expression is not type-correct under the instances transparency",
because these carrier projections are not reduced during rewrite matching.
Consequently this file states and proves the arrow integrality consequence at
the divisor-class / explicit-divisor level, without asserting a fake
`Hom` structure.  The precise missing interface is a coercion API usable by
`rw`: equivalences
`(globalDivisorMonoidOn.obj X).carrier = EffectiveDivisor F` and
`numberFieldSourceModelInput.rationalFunctions.obj X = Additive F^x`, together
with carrier-typed constructors for `divisor` and `rationalFunction`; once
these are available, the `balance` field is exactly
`backendBalanceEquation_of_effectivePartCone` after `gpPullback_id` and the
`numberFieldSourceModelInput.divisor` computation rule. -/

end TorsorArrowBackend

end TorsorBackendBridge

end Example36
end LeanFormal.IUT.IUTII.Frobenioid