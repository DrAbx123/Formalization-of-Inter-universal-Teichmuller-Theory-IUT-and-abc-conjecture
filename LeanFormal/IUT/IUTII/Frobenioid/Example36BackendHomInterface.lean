import LeanFormal.IUT.IUTII.Frobenioid.Example36TorsorBackendBridge
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelBackendBalanceGroup

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# The backend Horn interface: carrier coercions and the concrete model-Frobenioid arrow

`Example36TorsorBackendBridge` proved the object-level bridge between the
Example 3.6 torsor presentations and the model-Frobenioid object dictionary,
and the arrow-level balance consequence at the divisor-class level.  It also
reported the exact interface that was missing for assembling a concrete
`Iut.SourceModelFrobenioid.Hom`: the model carrier types
`(globalDivisorMonoidOn.obj X).carrier` and
`numberFieldSourceModelInput.rationalFunctions.obj X` are definitionally the
effective divisor cone and the additive group of units, but they do not reduce
during rewriting, so the `Hom` balance field could not be closed directly.

This file supplies that interface as *proved lemmas and definitions*, not as
structure fields:

1. rw-usable carrier equalities `backendDivisorCarrier_eq` and
   `backendRationalFunctionCarrier_eq` for every bottom-base object `X`;
2. carrier-typed constructors and coercions in both directions
   (`backendDivisorCarrierOfEffective`, `backendDivisorCarrierToEffective`,
   `backendRationalFunctionOfUnit`, `backendRationalFunctionToUnit`) with
   application and roundtrip `simp` lemmas;
3. the concrete model-Frobenioid arrow `idealFamilyHomToBackendHom` attached
   to a homomorphism of global ideal families over the actual number-field
   place data (Frobenius degree `h.degree`, base arrow the identity of
   `bottomPoint`, divisor the effective cone element `Z_+` of task 25,
   rational function the multiplier), with the `balance` field proved from
   `backendBalanceEquation_of_effectivePartCone`, plus the transported
   `TorsorArrow` version `torsorArrowToBackendHom`.

Boundary: model-Frobenioid arrows and divisor-group coordinates only; no
theta-pilot, q-pilot or source-identification claim.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open IsDedekindDomain NumberField
open scoped NumberField

universe u

variable {F : Type u} [Field F] [NumberField F]

namespace BackendHomInterface

/-! ## 1. rw-usable carrier equalities -/

/-- The model-Frobenioid divisor carrier at every bottom-base object is the
effective divisor cone. -/
theorem backendDivisorCarrier_eq (X : SourceModelBackend.BottomBase) :
    ((SourceModelBackend.globalDivisorMonoidOn (F := F)).obj X).carrier =
      SourceModelBackend.EffectiveDivisor F := rfl

/-- The model-Frobenioid rational-function carrier at every bottom-base object
is the additive group of units. -/
theorem backendRationalFunctionCarrier_eq (X : SourceModelBackend.BottomBase) :
    ((SourceModelBackend.numberFieldSourceModelInput (F := F)).rationalFunctions.obj X) =
      Additive Fˣ := rfl

/-! ## 2. Carrier-typed constructors and coercions -/

/-- View an effective divisor as an element of the model divisor carrier. -/
def backendDivisorCarrierOfEffective (X : SourceModelBackend.BottomBase)
    (Z : SourceModelBackend.EffectiveDivisor F) :
    ((SourceModelBackend.globalDivisorMonoidOn (F := F)).obj X).carrier := Z

/-- View an element of the model divisor carrier as an effective divisor. -/
def backendDivisorCarrierToEffective (X : SourceModelBackend.BottomBase)
    (z : ((SourceModelBackend.globalDivisorMonoidOn (F := F)).obj X).carrier) :
    SourceModelBackend.EffectiveDivisor F := z

@[simp]
theorem backendDivisorCarrierToEffective_ofEffective
    (X : SourceModelBackend.BottomBase) (Z : SourceModelBackend.EffectiveDivisor F) :
    backendDivisorCarrierToEffective X (backendDivisorCarrierOfEffective X Z) = Z := rfl

@[simp]
theorem backendDivisorCarrierOfEffective_toEffective
    (X : SourceModelBackend.BottomBase)
    (z : ((SourceModelBackend.globalDivisorMonoidOn (F := F)).obj X).carrier) :
    backendDivisorCarrierOfEffective X (backendDivisorCarrierToEffective X z) = z := rfl

/-- View a unit as an element of the model rational-function carrier. -/
def backendRationalFunctionOfUnit (X : SourceModelBackend.BottomBase) (f : Fˣ) :
    ((SourceModelBackend.numberFieldSourceModelInput (F := F)).rationalFunctions.obj X) :=
  Additive.ofMul f

/-- View an element of the model rational-function carrier as a unit. -/
def backendRationalFunctionToUnit (X : SourceModelBackend.BottomBase)
    (u : ((SourceModelBackend.numberFieldSourceModelInput (F := F)).rationalFunctions.obj X)) :
    Additive Fˣ := u

@[simp]
theorem backendRationalFunctionToUnit_ofUnit
    (X : SourceModelBackend.BottomBase) (f : Fˣ) :
    backendRationalFunctionToUnit X (backendRationalFunctionOfUnit X f) =
      Additive.ofMul f := rfl

@[simp]
theorem backendRationalFunctionOfUnit_toUnit
    (X : SourceModelBackend.BottomBase)
    (u : ((SourceModelBackend.numberFieldSourceModelInput (F := F)).rationalFunctions.obj X)) :
    backendRationalFunctionOfUnit X (backendRationalFunctionToUnit X u).toMul = u := rfl

/-- The divisor-carrier additive commutative monoid instance is the standard
one on the effective divisor cone. -/
theorem backendDivisorAddCommMonoid_eq (X : SourceModelBackend.BottomBase) :
    ((SourceModelBackend.globalDivisorMonoidOn (F := F)).obj X).addCommMonoid =
      (inferInstance : AddCommMonoid (SourceModelBackend.EffectiveDivisor F)) := rfl

/-- The rational-function-carrier additive commutative group instance is the
standard one on the additive group of units. -/
theorem backendRationalFunctionAddCommGroup_eq (X : SourceModelBackend.BottomBase) :
    ((SourceModelBackend.numberFieldSourceModelInput (F := F)).rationalFunctions.addCommGroup X) =
      (inferInstance : AddCommGroup (Additive Fˣ)) := rfl

/-- The divisor-carrier coercion is additive. -/
def backendDivisorCarrierAddEquiv (X : SourceModelBackend.BottomBase) :
    ((SourceModelBackend.globalDivisorMonoidOn (F := F)).obj X).carrier ≃+
      SourceModelBackend.EffectiveDivisor F where
  toFun := backendDivisorCarrierToEffective X
  invFun := backendDivisorCarrierOfEffective X
  left_inv z := backendDivisorCarrierOfEffective_toEffective X z
  right_inv Z := backendDivisorCarrierToEffective_ofEffective X Z
  map_add' a b := rfl

@[simp]
theorem backendDivisorCarrierAddEquiv_apply (X : SourceModelBackend.BottomBase)
    (z : ((SourceModelBackend.globalDivisorMonoidOn (F := F)).obj X).carrier) :
    backendDivisorCarrierAddEquiv X z = backendDivisorCarrierToEffective X z := rfl

/-- The induced identity isomorphism of Grothendieck groups. -/
def backendDivisorGrothendieckEquiv (X : SourceModelBackend.BottomBase) :
    Algebra.GrothendieckAddGroup
        ((SourceModelBackend.globalDivisorMonoidOn (F := F)).obj X).carrier ≃+
      Algebra.GrothendieckAddGroup (SourceModelBackend.EffectiveDivisor F) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The Frobenius degree of an ideal-family morphism as a positive natural. -/
def homDegreePNat {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₁ J₂) : ℕ+ :=
  ⟨h.degree, h.positive_degree⟩

@[simp]
theorem homDegreePNat_val {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₁ J₂) :
    (homDegreePNat h).val = h.degree := rfl

/-! ## 3. The concrete model-Frobenioid arrow -/

/-- The concrete model-Frobenioid arrow attached to a homomorphism of global
ideal families over the actual number-field place data. -/
noncomputable def idealFamilyHomToBackendHom
    {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₁ J₂) :
    Iut.SourceModelFrobenioid.Hom
      (SourceModelBackend.globalDivisorMonoidOn (F := F))
      (SourceModelBackend.numberFieldSourceModelInput (F := F))
      (SourceModelBackend.objectOfIdealFamily (F := F) J₁)
      (SourceModelBackend.objectOfIdealFamily (F := F) J₂) where
  frobeniusDegree := homDegreePNat h
  base := CategoryTheory.CategoryStruct.id SourceModelBackend.bottomPoint
  divisor := backendDivisorCarrierOfEffective
    (SourceModelBackend.objectOfIdealFamily (F := F) J₁).base
    (SourceModelBackendBalanceGroup.effectivePartCone
      (numberFieldGlobalPlaceData (F := F)) numberFieldGlobalPlaceData_hasFiniteSupport h)
  rationalFunction := backendRationalFunctionOfUnit
    (SourceModelBackend.objectOfIdealFamily (F := F) J₁).base h.multiplier
  balance := by
    rw [homDegreePNat_val]
    have htask := SourceModelBackendBalanceGroup.backendBalanceEquation_of_effectivePartCone h
    simp only [backendDivisorCarrier_eq, backendRationalFunctionCarrier_eq,
      backendDivisorAddCommMonoid_eq, backendRationalFunctionAddCommGroup_eq,
      Iut.SourceModelFrobenioid.gpPullback_id, AddMonoidHom.id_apply,
      backendDivisorCarrierOfEffective, backendRationalFunctionOfUnit,
      SourceModelBackend.numberFieldSourceModelInput,
      SourceModelBackend.objectOfIdealFamily, SourceModelBackend.globalModelDivisor,
      AddMonoidHom.comp_apply]
    exact htask

/-- The concrete model-Frobenioid arrow has the intended Frobenius degree. -/
@[simp]
theorem idealFamilyHomToBackendHom_frobeniusDegree_val
    {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₁ J₂) :
    (idealFamilyHomToBackendHom h).frobeniusDegree.val = h.degree := rfl

/-- The concrete model-Frobenioid arrow has the identity base arrow. -/
@[simp]
theorem idealFamilyHomToBackendHom_base
    {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₁ J₂) :
    (idealFamilyHomToBackendHom h).base =
      CategoryTheory.CategoryStruct.id SourceModelBackend.bottomPoint := rfl

/-- The divisor field of the concrete model-Frobenioid arrow is the effective
cone element `Z_+`. -/
@[simp]
theorem idealFamilyHomToBackendHom_divisor
    {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₁ J₂) :
    (idealFamilyHomToBackendHom h).divisor =
      backendDivisorCarrierOfEffective
        (SourceModelBackend.objectOfIdealFamily (F := F) J₁).base
        (SourceModelBackendBalanceGroup.effectivePartCone
          (numberFieldGlobalPlaceData (F := F))
          numberFieldGlobalPlaceData_hasFiniteSupport h) := rfl

/-- The rational-function field of the concrete model-Frobenioid arrow is the
multiplier `ofMul f`. -/
@[simp]
theorem idealFamilyHomToBackendHom_rationalFunction
    {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₁ J₂) :
    (idealFamilyHomToBackendHom h).rationalFunction =
      backendRationalFunctionOfUnit
        (SourceModelBackend.objectOfIdealFamily (F := F) J₁).base h.multiplier := rfl

/-- The balance field of the concrete model-Frobenioid arrow, in the readable
group-completion form (the same identity as the task-25 backend balance). -/
theorem idealFamilyHomToBackendHom_balance
    {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₁ J₂) :
    (h.degree : ℕ) • SourceModelBackend.idealFamilyDivisorClass (F := F) J₁ +
        Algebra.GrothendieckAddGroup.of
          (SourceModelBackendBalanceGroup.effectivePartCone
            (numberFieldGlobalPlaceData (F := F))
            numberFieldGlobalPlaceData_hasFiniteSupport h) =
      SourceModelBackend.idealFamilyDivisorClass (F := F) J₂ +
        SourceModelBackend.globalModelDivisor (F := F)
          (Additive.ofMul h.multiplier) :=
  SourceModelBackendBalanceGroup.backendBalanceEquation_of_effectivePartCone h

/-! ## 4. The concrete arrow attached to a torsor arrow -/

section TorsorArrowBackend

variable {P₁ P₂ : TorsorPresentation (numberFieldGlobalPlaceData (F := F))}

/-- The concrete model-Frobenioid arrow attached to a torsor arrow, by
transporting the arrow through the coordinate equivalence and applying the
backend Hom construction. -/
noncomputable def torsorArrowToBackendHom (φ : TorsorArrow P₁ P₂) :
    Iut.SourceModelFrobenioid.Hom
      (SourceModelBackend.globalDivisorMonoidOn (F := F))
      (SourceModelBackend.numberFieldSourceModelInput (F := F))
      (SourceModelBackend.objectOfIdealFamily (F := F)
        (presentationToIdealFamily (numberFieldGlobalPlaceData (F := F)) P₁))
      (SourceModelBackend.objectOfIdealFamily (F := F)
        (presentationToIdealFamily (numberFieldGlobalPlaceData (F := F)) P₂)) :=
  idealFamilyHomToBackendHom
    (presentationArrowToIdealFamilyHom (numberFieldGlobalPlaceData (F := F)) φ)

/-- The Frobenius degree of the model-Frobenioid arrow of a torsor arrow. -/
@[simp]
theorem torsorArrowToBackendHom_frobeniusDegree_val (φ : TorsorArrow P₁ P₂) :
    (torsorArrowToBackendHom φ).frobeniusDegree.val = φ.degree := rfl

/-- The base arrow of the model-Frobenioid arrow of a torsor arrow is the
identity of `bottomPoint`. -/
@[simp]
theorem torsorArrowToBackendHom_base (φ : TorsorArrow P₁ P₂) :
    (torsorArrowToBackendHom φ).base =
      CategoryTheory.CategoryStruct.id SourceModelBackend.bottomPoint := rfl

/-- The balance identity of the model-Frobenioid arrow of a torsor arrow, in
the readable group-completion form. -/
theorem torsorArrowToBackendHom_balance (φ : TorsorArrow P₁ P₂) :
    (φ.degree : ℕ) • SourceModelBackend.idealFamilyDivisorClass (F := F)
        (presentationToIdealFamily (numberFieldGlobalPlaceData (F := F)) P₁) +
        Algebra.GrothendieckAddGroup.of
          (SourceModelBackendBalanceGroup.effectivePartCone
            (numberFieldGlobalPlaceData (F := F))
            numberFieldGlobalPlaceData_hasFiniteSupport
            (presentationArrowToIdealFamilyHom (numberFieldGlobalPlaceData (F := F)) φ)) =
      SourceModelBackend.idealFamilyDivisorClass (F := F)
        (presentationToIdealFamily (numberFieldGlobalPlaceData (F := F)) P₂) +
        SourceModelBackend.globalModelDivisor (F := F) (Additive.ofMul φ.multiplier) := by
  simpa only [torsorArrowToBackendHom, idealFamilyHomToBackendHom,
    presentationArrowToIdealFamilyHom_degree,
    presentationArrowToIdealFamilyHom_multiplier] using
    SourceModelBackendBalanceGroup.backendBalanceEquation_of_effectivePartCone
      (presentationArrowToIdealFamilyHom (numberFieldGlobalPlaceData (F := F)) φ)

end TorsorArrowBackend

end BackendHomInterface

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
