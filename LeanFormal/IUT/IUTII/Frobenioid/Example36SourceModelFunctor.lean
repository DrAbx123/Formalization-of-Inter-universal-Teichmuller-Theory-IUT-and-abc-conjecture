import LeanFormal.IUT.IUTII.Frobenioid.Example36BackendHomInterface
import LeanFormal.IUT.IUTII.Frobenioid.Example36TorsorBackendBridge

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# The functor from global ideal families to the model Frobenioid category

This file packages the object/arrow dictionary of
`Example36BackendHomInterface` as a functor from the category of global ideal
families (over the actual number-field place data, with the Example 3.6 arrow
category structure) to the explicit model-Frobenioid category
`Iut.SourceModelFrobenioid.Carrier`.

Contents:

1. the category structure on `GlobalIdealFamily F` whose morphisms are
   `GlobalIdealFamily.Hom numberFieldGlobalPlaceData` (the identity and
   composition laws are the ones already proved in
   `Example36GlobalIdealFamily`);
2. auxiliary lemmas on the effective cone element and on the carrier
   coercions (identity, composition of effective parts, additivity of the
   divisor coercion, and the `ofMul`/power law for rational functions);
3. the functor `sourceModelFunctor` with `obj J = objectOfIdealFamily J` and
   `map h = idealFamilyHomToBackendHom h`, together with `map_id`, `map_comp`
   and the field computation laws for `frobeniusDegree`, `base`, `divisor`
   and `rationalFunction`.

Boundary: this is the arithmetic-divisor/model-carrier dictionary only; no
theta-pilot, q-pilot or source-identification claim.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open IsDedekindDomain NumberField
open scoped NumberField

universe u

variable {F : Type u} [Field F] [NumberField F]

namespace SourceModelFunctor

/-! ## 1. The category of global ideal families -/

/-- The category of global ideal families over a fixed place data `D`:
morphisms are `GlobalIdealFamily.Hom D`. -/
@[reducible]
def idealFamilyCategory (D : GlobalPlaceData F) :
    CategoryTheory.Category.{u, u} (GlobalIdealFamily F) where
  Hom J₁ J₂ := GlobalIdealFamily.Hom D J₁ J₂
  id J := GlobalIdealFamily.Hom.id (D := D) J
  comp h k := GlobalIdealFamily.Hom.comp h k
  id_comp h := GlobalIdealFamily.Hom.id_comp (D := D) h
  comp_id h := GlobalIdealFamily.Hom.comp_id (D := D) h
  assoc h k l := GlobalIdealFamily.Hom.comp_assoc (D := D) h k l

/-- The category of global ideal families over the actual number-field place
data. -/
instance numberFieldIdealFamilyCategory :
    CategoryTheory.Category.{u, u} (GlobalIdealFamily F) :=
  idealFamilyCategory (numberFieldGlobalPlaceData (F := F))
/-- All endomorphisms in the bottom base category are equal (they are
`ULift Unit`). -/
instance bottomBaseHomSubsingleton {X Y : SourceModelBackend.BottomBase} :
    Subsingleton (X ⟶ Y) where
  allEq _ _ := Subsingleton.elim (α := ULift Unit) _ _

/-! ## 2. Auxiliary lemmas -/

/-- Integer `toNat` of a sum of nonnegative integers is the sum of the
`toNat`s. -/
theorem int_toNat_add_of_nonneg (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b).toNat = a.toNat + b.toNat := by
  have h : ((a + b).toNat : ℤ) = ((a.toNat + b.toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg (add_nonneg ha hb), Nat.cast_add,
      Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb]
  exact_mod_cast h

/-- Integer `toNat` of a natural multiple of a nonnegative integer. -/
theorem int_toNat_natCast_mul (n : ℕ) {a : ℤ} (ha : 0 ≤ a) :
    (((n : ℤ) * a).toNat) = n * a.toNat := by
  have h : (((n : ℤ) * a).toNat : ℤ) = ((n * a.toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg (mul_nonneg (Nat.cast_nonneg n) ha), Nat.cast_mul,
      Int.toNat_of_nonneg ha]
  exact_mod_cast h

/-- `Real.toNNReal` of a natural multiple of a nonnegative real number. -/
theorem real_toNNReal_natCast_mul (n : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    ((n : ℝ) * a).toNNReal = n • a.toNNReal := by
  apply NNReal.coe_injective
  rw [Real.coe_toNNReal ((n : ℝ) * a) (mul_nonneg (Nat.cast_nonneg n) ha),
    NNReal.coe_nsmul, Real.coe_toNNReal a ha, nsmul_eq_mul]

/-- The divisor-carrier coercion preserves addition. -/
@[simp]
theorem backendDivisorCarrierOfEffective_add (X : SourceModelBackend.BottomBase)
    (Z W : SourceModelBackend.EffectiveDivisor F) :
    BackendHomInterface.backendDivisorCarrierOfEffective X (Z + W) =
      BackendHomInterface.backendDivisorCarrierOfEffective X Z +
        BackendHomInterface.backendDivisorCarrierOfEffective X W := rfl

/-- The divisor-carrier coercion preserves natural multiples. -/
@[simp]
theorem backendDivisorCarrierOfEffective_nsmul (X : SourceModelBackend.BottomBase)
    (n : ℕ) (Z : SourceModelBackend.EffectiveDivisor F) :
    BackendHomInterface.backendDivisorCarrierOfEffective X (n • Z) =
      n • BackendHomInterface.backendDivisorCarrierOfEffective X Z := rfl

/-- The divisor-carrier coercion sends zero to zero. -/
@[simp]
theorem backendDivisorCarrierOfEffective_zero (X : SourceModelBackend.BottomBase) :
    BackendHomInterface.backendDivisorCarrierOfEffective X
      (0 : SourceModelBackend.EffectiveDivisor F) = 0 := rfl

/-- The coercion `Additive.ofMul` is additive. -/
theorem addOfMul_mul (f g : Fˣ) :
    Additive.ofMul (f * g) = Additive.ofMul f + Additive.ofMul g := rfl

/-- The power of a unit is its natural multiple in the additive notation. -/
theorem addOfMul_pow (n : ℕ) (f : Fˣ) :
    Additive.ofMul (f ^ n) = n • Additive.ofMul f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ, addOfMul_mul, ih, succ_nsmul]

/-- The rational-function coercion preserves addition (multiplication of
units). -/
@[simp]
theorem backendRationalFunctionOfUnit_mul (X : SourceModelBackend.BottomBase)
    (f g : Fˣ) :
    BackendHomInterface.backendRationalFunctionOfUnit X (f * g) =
      BackendHomInterface.backendRationalFunctionOfUnit X f +
        BackendHomInterface.backendRationalFunctionOfUnit X g := by
  simp only [BackendHomInterface.backendRationalFunctionOfUnit]
  exact addOfMul_mul f g

/-- The natural multiple of a rational-function carrier element is the
coercion of the power. -/
@[simp]
theorem backendRationalFunctionOfUnit_pow (X : SourceModelBackend.BottomBase)
    (n : ℕ) (f : Fˣ) :
    n • BackendHomInterface.backendRationalFunctionOfUnit X f =
      BackendHomInterface.backendRationalFunctionOfUnit X (f ^ n) := by
  simp only [BackendHomInterface.backendRationalFunctionOfUnit]
  exact (addOfMul_pow n f).symm


/-- The rational-function coercion is additive on the wrapped carrier element. -/
theorem backendRationalFunctionOfUnit_mul_wrapped (X : SourceModelBackend.BottomBase)
    (f g : Fˣ) :
    BackendHomInterface.backendRationalFunctionOfUnit X (f * g) =
      BackendHomInterface.backendRationalFunctionOfUnit X f +
        BackendHomInterface.backendRationalFunctionOfUnit X g := rfl

/-- The natural multiple of the wrapped rational-function element is the
coercion of the power. -/
theorem backendRationalFunctionOfUnit_pow_wrapped (X : SourceModelBackend.BottomBase)
    (n : ℕ) (f : Fˣ) :
    n • BackendHomInterface.backendRationalFunctionOfUnit X f =
      BackendHomInterface.backendRationalFunctionOfUnit X (f ^ n) := by
  change n • Additive.ofMul f = Additive.ofMul (f ^ n)
  exact (addOfMul_pow n f).symm

/-- The wrapped rational-function element of the unit `1` is zero. -/
theorem backendRationalFunctionOfUnit_one (X : SourceModelBackend.BottomBase) :
    BackendHomInterface.backendRationalFunctionOfUnit X (1 : Fˣ) = 0 := rfl

/-- The effective cone element of the identity morphism is zero. -/
theorem effectivePartCone_id (D : GlobalPlaceData F) (hD : D.HasFiniteSupport)
    (J : GlobalIdealFamily F) :
    SourceModelBackendBalanceGroup.effectivePartCone D hD
      (GlobalIdealFamily.Hom.id (D := D) J) = 0 := by
  apply Prod.ext
  · ext v
    rw [SourceModelBackendBalanceGroup.effectivePartCone_fst_apply]
    have h0 : (GlobalIdealFamily.Hom.id (D := D) J).effectiveFinite v = 0 := by
      simp [GlobalIdealFamily.Hom.effectiveFinite, GlobalIdealFamily.Hom.id,
        GlobalPlaceData.finiteDelta_one]
    rw [h0]
    rfl
  · funext w
    rw [SourceModelBackendBalanceGroup.effectivePartCone_snd_apply]
    have h0 : (GlobalIdealFamily.Hom.id (D := D) J).effectiveInfinite w = 0 := by
      simp [GlobalIdealFamily.Hom.effectiveInfinite, GlobalIdealFamily.Hom.id,
        GlobalPlaceData.infiniteDelta_one]
    rw [h0, Real.toNNReal_zero]
    simp

/-! ## 3. Composition of the effective part and the functor laws -/

/-- **The effective part is compatible with composition.**  For `h : J₁ → J₂`
and `k : J₂ → J₃` over the number-field place data,
`Z(k ∘ h) = Z(k) + k.degree • Z(h)`. -/
theorem effectivePartCone_comp {J₁ J₂ J₃ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₁ J₂)
    (k : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₂ J₃) :
    SourceModelBackendBalanceGroup.effectivePartCone
        (numberFieldGlobalPlaceData (F := F))
        numberFieldGlobalPlaceData_hasFiniteSupport
        (GlobalIdealFamily.Hom.comp h k) =
      SourceModelBackendBalanceGroup.effectivePartCone
          (numberFieldGlobalPlaceData (F := F))
          numberFieldGlobalPlaceData_hasFiniteSupport k +
        k.degree • SourceModelBackendBalanceGroup.effectivePartCone
          (numberFieldGlobalPlaceData (F := F))
          numberFieldGlobalPlaceData_hasFiniteSupport h := by
  have hk_nonneg : ∀ v, (0 : ℤ) ≤ k.effectiveFinite v := by
    intro v
    have hc := k.effectiveFinite_mem_cone v
    simpa [numberFieldGlobalPlaceData, numberFieldFiniteLocalValueData,
      integerNonnegCone] using hc
  have hh_nonneg : ∀ v, (0 : ℤ) ≤ h.effectiveFinite v := by
    intro v
    have hc := h.effectiveFinite_mem_cone v
    simpa [numberFieldGlobalPlaceData, numberFieldFiniteLocalValueData,
      integerNonnegCone] using hc
  have hk_nonneg_inf : ∀ w, (0 : ℝ) ≤ k.effectiveInfinite w := by
    intro w
    have hc := k.effectiveInfinite_mem_cone w
    simpa [numberFieldGlobalPlaceData, numberFieldInfiniteLocalValueData,
      realNonnegCone] using hc
  have hh_nonneg_inf : ∀ w, (0 : ℝ) ≤ h.effectiveInfinite w := by
    intro w
    have hc := h.effectiveInfinite_mem_cone w
    simpa [numberFieldGlobalPlaceData, numberFieldInfiniteLocalValueData,
      realNonnegCone] using hc
  apply Prod.ext
  · ext v
    simp only [Prod.fst_add, Prod.smul_fst, Finsupp.add_apply, Finsupp.nsmul_apply,
      SourceModelBackendBalanceGroup.effectivePartCone_fst_apply]
    have hsum : (GlobalIdealFamily.Hom.comp h k).effectiveFinite v =
        k.effectiveFinite v + (k.degree : ℤ) * h.effectiveFinite v := by
      simp only [GlobalIdealFamily.Hom.comp, GlobalIdealFamily.Hom.effectiveFinite,
        GlobalPlaceData.finiteDelta_mul, GlobalPlaceData.finiteDelta_pow]
      ring
    have hnat := int_toNat_add_of_nonneg (k.effectiveFinite v)
      ((k.degree : ℤ) * h.effectiveFinite v) (hk_nonneg v)
      (mul_nonneg (Nat.cast_nonneg k.degree) (hh_nonneg v))
    rw [hsum, hnat, int_toNat_natCast_mul k.degree (hh_nonneg v), nsmul_eq_mul]
    simp
  · funext w
    simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply,
      SourceModelBackendBalanceGroup.effectivePartCone_snd_apply]
    have hsum : (GlobalIdealFamily.Hom.comp h k).effectiveInfinite w =
        k.effectiveInfinite w + (k.degree : ℝ) * h.effectiveInfinite w := by
      simp only [GlobalIdealFamily.Hom.comp, GlobalIdealFamily.Hom.effectiveInfinite,
        GlobalPlaceData.infiniteDelta_mul, GlobalPlaceData.infiniteDelta_pow]
      ring
    rw [hsum, Real.toNNReal_add (hk_nonneg_inf w)
        (mul_nonneg (Nat.cast_nonneg k.degree) (hh_nonneg_inf w)),
      real_toNNReal_natCast_mul k.degree (hh_nonneg_inf w)]

/-- The ideal-family identity maps to the identity of the model Frobenioid. -/
theorem idealFamilyHomToBackendHom_id (J : GlobalIdealFamily F) :
    BackendHomInterface.idealFamilyHomToBackendHom
        (GlobalIdealFamily.Hom.id (D := numberFieldGlobalPlaceData (F := F)) J) =
      Iut.SourceModelFrobenioid.Hom.id
        (SourceModelBackend.globalDivisorMonoidOn (F := F))
        (SourceModelBackend.numberFieldSourceModelInput (F := F))
        (SourceModelBackend.objectOfIdealFamily (F := F) J) := by
  apply Iut.SourceModelFrobenioid.Hom.ext
  · rfl
  · exact Subsingleton.elim _ _
  · simp only [BackendHomInterface.idealFamilyHomToBackendHom_divisor,
      Iut.SourceModelFrobenioid.Hom.id, effectivePartCone_id,
      backendDivisorCarrierOfEffective_zero]
  · simp only [BackendHomInterface.idealFamilyHomToBackendHom_rationalFunction,
      Iut.SourceModelFrobenioid.Hom.id, GlobalIdealFamily.Hom.id]
    exact backendRationalFunctionOfUnit_one _

/-- Composition of ideal-family morphisms maps to composition of the model
Frobenioid arrows. -/
theorem idealFamilyHomToBackendHom_comp {J₁ J₂ J₃ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₁ J₂)
    (k : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₂ J₃) :
    BackendHomInterface.idealFamilyHomToBackendHom
        (GlobalIdealFamily.Hom.comp h k) =
      Iut.SourceModelFrobenioid.Hom.comp
        (SourceModelBackend.globalDivisorMonoidOn (F := F))
        (SourceModelBackend.numberFieldSourceModelInput (F := F))
        (BackendHomInterface.idealFamilyHomToBackendHom h)
        (BackendHomInterface.idealFamilyHomToBackendHom k) := by
  apply Iut.SourceModelFrobenioid.Hom.ext
  · apply Subtype.ext
    simp only [BackendHomInterface.idealFamilyHomToBackendHom_frobeniusDegree_val,
      Iut.SourceModelFrobenioid.Hom.comp, GlobalIdealFamily.Hom.comp]
    exact Nat.mul_comm k.degree h.degree
  · exact Subsingleton.elim _ _
  · show BackendHomInterface.backendDivisorCarrierOfEffective
        (SourceModelBackend.objectOfIdealFamily (F := F) J₁).base
        (SourceModelBackendBalanceGroup.effectivePartCone
          (numberFieldGlobalPlaceData (F := F))
          numberFieldGlobalPlaceData_hasFiniteSupport
          (GlobalIdealFamily.Hom.comp h k)) =
      BackendHomInterface.backendDivisorCarrierOfEffective
        (SourceModelBackend.objectOfIdealFamily (F := F) J₁).base
        (SourceModelBackendBalanceGroup.effectivePartCone
            (numberFieldGlobalPlaceData (F := F))
            numberFieldGlobalPlaceData_hasFiniteSupport k +
          k.degree • SourceModelBackendBalanceGroup.effectivePartCone
            (numberFieldGlobalPlaceData (F := F))
            numberFieldGlobalPlaceData_hasFiniteSupport h)
    exact congrArg (BackendHomInterface.backendDivisorCarrierOfEffective
      (SourceModelBackend.objectOfIdealFamily (F := F) J₁).base)
      (effectivePartCone_comp h k)
  · show BackendHomInterface.backendRationalFunctionOfUnit
        (SourceModelBackend.objectOfIdealFamily (F := F) J₁).base
        (GlobalIdealFamily.Hom.comp h k).multiplier =
      BackendHomInterface.backendRationalFunctionOfUnit
          (SourceModelBackend.objectOfIdealFamily (F := F) J₁).base k.multiplier +
        k.degree • BackendHomInterface.backendRationalFunctionOfUnit
          (SourceModelBackend.objectOfIdealFamily (F := F) J₁).base h.multiplier
    rw [backendRationalFunctionOfUnit_pow_wrapped,
      ← backendRationalFunctionOfUnit_mul_wrapped]
    rfl

/-! ## 4. The functor -/

/-- The functor from the category of global ideal families (Example 3.6 arrow
category) to the model-Frobenioid category: objects are the backend objects
`objectOfIdealFamily J`, and arrows are the concrete model-Frobenioid arrows
`idealFamilyHomToBackendHom h`. -/
noncomputable def sourceModelFunctor :
    @CategoryTheory.Functor (GlobalIdealFamily F)
      (numberFieldIdealFamilyCategory (F := F))
      (Iut.SourceModelFrobenioid.Carrier
        (SourceModelBackend.globalDivisorMonoidOn (F := F))
        (SourceModelBackend.numberFieldSourceModelInput (F := F)))
      (Iut.SourceModelFrobenioid.carrierCategory
        (SourceModelBackend.globalDivisorMonoidOn (F := F))
        (SourceModelBackend.numberFieldSourceModelInput (F := F))) where
  obj J := SourceModelBackend.objectOfIdealFamily (F := F) J
  map h := BackendHomInterface.idealFamilyHomToBackendHom h
  map_id J := idealFamilyHomToBackendHom_id J
  map_comp h k := idealFamilyHomToBackendHom_comp h k

@[simp]
theorem sourceModelFunctor_obj (J : GlobalIdealFamily F) :
    sourceModelFunctor.obj J = SourceModelBackend.objectOfIdealFamily (F := F) J := rfl

@[simp]
theorem sourceModelFunctor_map {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₁ J₂) :
    sourceModelFunctor.map h =
      BackendHomInterface.idealFamilyHomToBackendHom h := rfl

/-- `map_id`: the functor preserves identities. -/
@[simp]
theorem sourceModelFunctor_map_id (J : GlobalIdealFamily F) :
    sourceModelFunctor.map (CategoryTheory.CategoryStruct.id J) =
      CategoryTheory.CategoryStruct.id (sourceModelFunctor.obj J) :=
  sourceModelFunctor.map_id J

/-- `map_comp`: the functor preserves composition. -/
@[simp]
theorem sourceModelFunctor_map_comp {J₁ J₂ J₃ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₁ J₂)
    (k : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₂ J₃) :
    sourceModelFunctor.map (CategoryTheory.CategoryStruct.comp h k) =
      CategoryTheory.CategoryStruct.comp
        (sourceModelFunctor.map h) (sourceModelFunctor.map k) :=
  sourceModelFunctor.map_comp h k

/-! ## 5. Field computation laws -/

/-- The Frobenius degree of the image arrow is the degree of the ideal-family
morphism. -/
@[simp]
theorem sourceModelFunctor_map_frobeniusDegree_val {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₁ J₂) :
    (sourceModelFunctor.map h).frobeniusDegree.val = h.degree :=
  BackendHomInterface.idealFamilyHomToBackendHom_frobeniusDegree_val h

/-- The base arrow of the image arrow is the identity of `bottomPoint`. -/
@[simp]
theorem sourceModelFunctor_map_base {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₁ J₂) :
    (sourceModelFunctor.map h).base =
      CategoryTheory.CategoryStruct.id SourceModelBackend.bottomPoint :=
  BackendHomInterface.idealFamilyHomToBackendHom_base h

/-- The divisor of the image arrow is the effective cone element `Z_+`. -/
@[simp]
theorem sourceModelFunctor_map_divisor {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₁ J₂) :
    (sourceModelFunctor.map h).divisor =
      BackendHomInterface.backendDivisorCarrierOfEffective
        (SourceModelBackend.objectOfIdealFamily (F := F) J₁).base
        (SourceModelBackendBalanceGroup.effectivePartCone
          (numberFieldGlobalPlaceData (F := F))
          numberFieldGlobalPlaceData_hasFiniteSupport h) :=
  BackendHomInterface.idealFamilyHomToBackendHom_divisor h

/-- The rational function of the image arrow is the multiplier `ofMul f`. -/
@[simp]
theorem sourceModelFunctor_map_rationalFunction {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₁ J₂) :
    (sourceModelFunctor.map h).rationalFunction =
      BackendHomInterface.backendRationalFunctionOfUnit
        (SourceModelBackend.objectOfIdealFamily (F := F) J₁).base h.multiplier :=
  BackendHomInterface.idealFamilyHomToBackendHom_rationalFunction h

end SourceModelFunctor

end Example36
end LeanFormal.IUT.IUTII.Frobenioid