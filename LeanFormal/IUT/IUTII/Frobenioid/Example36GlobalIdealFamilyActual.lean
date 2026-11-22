import LeanFormal.IUT.IUTII.Frobenioid.Example36GlobalIdealFamily
import LeanFormal.IUT.IUTII.Frobenioid.Example36NumberFieldPlaceData

/-!
# The actual arithmetic instance of the global ideal-family category

This is the Layer-2 assembly.  It instantiates the global ideal-family category
of Example 3.6 at the genuine arithmetic place data of a number field:

* the finite places use the actual v-adic valuation exponents;
* the archimedean places use the actual absolute values with coordinate
  -log (w x).

The principal divisor of a global unit f is a genuine object
(principalDivisor f) built from the finitely supported valuation exponents and
the archimedean logarithms.  The translation of any ideal family by a principal
divisor,

  (1, f) : J --> J + div(f),

is a morphism of the category, and it is an isomorphism: its effective part
vanishes identically.  Composing two such translations reproduces the
Frobenioid composition rule (1,g) o (1,f) = (1, g f).  More generally the
degree-n arrow J --> n J + div(f) is a morphism.

Boundary: this file constructs the actual instance of the global ideal-family
category of Example 3.6 only.  It does not construct the torsor category or the
equivalence (next layer), nor the source Hodge theater / theta-pilot
identification.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open scoped NumberField
open IsDedekindDomain NumberField

universe u

variable {F : Type u} [Field F] [NumberField F]

/-- The principal divisor of a global unit f, as a global ideal-family object in
value coordinates: finitely supported v-adic exponents and archimedean
-log (w f). -/
def principalDivisor (f : Fˣ) : GlobalIdealFamily F :=
  ⟨principalDivisorFinite f, principalDivisorInfinite f⟩

@[simp]
theorem principalDivisor_finite (f : Fˣ) :
    (principalDivisor f).finite = principalDivisorFinite f := rfl

@[simp]
theorem principalDivisor_infinite (f : Fˣ) (w : NumberField.InfinitePlace F) :
    (principalDivisor f).infinite w = principalDivisorInfinite f w := rfl

@[simp]
theorem principalDivisor_finite_apply (f : Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (principalDivisor f).finite v = finitePlaceValueExponent v f :=
  principalDivisorFinite_apply f v

@[simp]
theorem principalDivisor_infinite_apply (f : Fˣ) (w : NumberField.InfinitePlace F) :
    (principalDivisor f).infinite w = -Real.log (w (f : F)) :=
  principalDivisorInfinite_apply f w

@[simp]
theorem principalDivisor_zero : principalDivisor (1 : Fˣ) = 0 := by
  ext <;> simp [principalDivisor]

theorem principalDivisor_mul (f g : Fˣ) :
    principalDivisor (f * g) = principalDivisor f + principalDivisor g := by
  ext <;> simp [principalDivisor, principalDivisorFinite_mul, principalDivisorInfinite_mul]

/-- The degree-one translation arrow (1,f): J --> J + div(f). -/
def principalArrow (J : GlobalIdealFamily F) (f : Fˣ) :
    GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J
      (J + principalDivisor f) where
  degree := 1
  positive_degree := Nat.one_pos
  multiplier := f
  finite_incl v := by
    show (numberFieldGlobalPlaceData (F := F)).finiteDelta f v + 1 • J.finite v -
      (J + principalDivisor f).finite v ∈ (numberFieldFiniteLocalValueData v).cone
    rw [show (J + principalDivisor f).finite v =
        J.finite v + (numberFieldGlobalPlaceData (F := F)).finiteDelta f v from by
      simp [GlobalIdealFamily.add_finite, principalDivisor]]
    have h0 : (numberFieldGlobalPlaceData (F := F)).finiteDelta f v + 1 • J.finite v -
        (J.finite v + (numberFieldGlobalPlaceData (F := F)).finiteDelta f v) = 0 := by
      abel
    rw [h0]
    exact (numberFieldFiniteLocalValueData v).cone.zero_mem
  infinite_incl w := by
    show (numberFieldGlobalPlaceData (F := F)).infiniteDelta f w + 1 • J.infinite w -
      (J + principalDivisor f).infinite w ∈ (numberFieldInfiniteLocalValueData w).cone
    rw [show (J + principalDivisor f).infinite w =
        J.infinite w + (numberFieldGlobalPlaceData (F := F)).infiniteDelta f w from by
      simp [GlobalIdealFamily.add_infinite, principalDivisor]]
    have h0 : (numberFieldGlobalPlaceData (F := F)).infiniteDelta f w + 1 • J.infinite w -
        (J.infinite w + (numberFieldGlobalPlaceData (F := F)).infiniteDelta f w) = 0 := by
      ring
    rw [h0]
    exact (numberFieldInfiniteLocalValueData w).cone.zero_mem

/-- Every principal translation is an isomorphism of the category. -/
theorem principalArrow_isIso (J : GlobalIdealFamily F) (f : Fˣ) :
    (principalArrow J f).IsIso := by
  apply GlobalIdealFamily.Hom.isIso_of_degree_one_of_effective_zero
  · rfl
  · constructor
    · intro v
      show (numberFieldGlobalPlaceData (F := F)).finiteDelta f v + 1 • J.finite v -
        (J + principalDivisor f).finite v = 0
      rw [show (J + principalDivisor f).finite v =
          J.finite v + (numberFieldGlobalPlaceData (F := F)).finiteDelta f v from by
        simp [GlobalIdealFamily.add_finite, principalDivisor]]
      abel
    · intro w
      show (numberFieldGlobalPlaceData (F := F)).infiniteDelta f w + 1 • J.infinite w -
        (J + principalDivisor f).infinite w = 0
      rw [show (J + principalDivisor f).infinite w =
          J.infinite w + (numberFieldGlobalPlaceData (F := F)).infiniteDelta f w from by
        simp [GlobalIdealFamily.add_infinite, principalDivisor]]
      ring

/-- The composition of two principal translations has degree one and
multiplier g f, matching the Frobenioid rule (1,g) o (1,f) = (1, g f). -/
theorem principalArrow_comp_degree (J : GlobalIdealFamily F) (f g : Fˣ) :
    (GlobalIdealFamily.Hom.comp (principalArrow J f)
      (principalArrow (J + principalDivisor f) g)).degree = 1 := rfl

theorem principalArrow_comp_multiplier (J : GlobalIdealFamily F) (f g : Fˣ) :
    (GlobalIdealFamily.Hom.comp (principalArrow J f)
      (principalArrow (J + principalDivisor f) g)).multiplier = g * f := by
  simp [GlobalIdealFamily.Hom.comp, principalArrow]

/-- The composition of two principal translations is again an isomorphism. -/
theorem principalArrow_comp_isIso (J : GlobalIdealFamily F) (f g : Fˣ) :
    (GlobalIdealFamily.Hom.comp (principalArrow J f)
      (principalArrow (J + principalDivisor f) g)).IsIso := by
  apply GlobalIdealFamily.Hom.isIso_of_degree_one_of_effective_zero
  · rfl
  · constructor
    · intro v
      have hdeg : (GlobalIdealFamily.Hom.comp (principalArrow J f)
          (principalArrow (J + principalDivisor f) g)).degree = 1 := rfl
      have hmult : (GlobalIdealFamily.Hom.comp (principalArrow J f)
          (principalArrow (J + principalDivisor f) g)).multiplier = g * f :=
        principalArrow_comp_multiplier J f g
      unfold GlobalIdealFamily.Hom.effectiveFinite
      rw [hmult, hdeg, one_nsmul]
      have hdelta : (numberFieldGlobalPlaceData (F := F)).finiteDelta (g * f) v =
          (numberFieldGlobalPlaceData (F := F)).finiteDelta g v +
            (numberFieldGlobalPlaceData (F := F)).finiteDelta f v := by
        simp [GlobalPlaceData.finiteDelta, LocalValueData.deltaAdd_mul]
      rw [hdelta]
      have htarget : ((J + principalDivisor f) + principalDivisor g).finite v =
          J.finite v + (numberFieldGlobalPlaceData (F := F)).finiteDelta f v +
            (numberFieldGlobalPlaceData (F := F)).finiteDelta g v := by
        simp [GlobalIdealFamily.add_finite, principalDivisor]
      rw [htarget]
      abel
    · intro w
      have hdeg : (GlobalIdealFamily.Hom.comp (principalArrow J f)
          (principalArrow (J + principalDivisor f) g)).degree = 1 := rfl
      have hmult : (GlobalIdealFamily.Hom.comp (principalArrow J f)
          (principalArrow (J + principalDivisor f) g)).multiplier = g * f :=
        principalArrow_comp_multiplier J f g
      unfold GlobalIdealFamily.Hom.effectiveInfinite
      rw [hmult, hdeg, one_nsmul]
      have hdelta : (numberFieldGlobalPlaceData (F := F)).infiniteDelta (g * f) w =
          (numberFieldGlobalPlaceData (F := F)).infiniteDelta g w +
            (numberFieldGlobalPlaceData (F := F)).infiniteDelta f w := by
        simp [GlobalPlaceData.infiniteDelta, LocalValueData.deltaAdd_mul]
      rw [hdelta]
      have htarget : ((J + principalDivisor f) + principalDivisor g).infinite w =
          J.infinite w + (numberFieldGlobalPlaceData (F := F)).infiniteDelta f w +
            (numberFieldGlobalPlaceData (F := F)).infiniteDelta g w := by
        simp [GlobalIdealFamily.add_infinite, principalDivisor]
      rw [htarget]
      ring

/-- The degree-n dilation arrow J --> n J + div(f), for positive n. -/
def powerTranslationArrow (J : GlobalIdealFamily F) (f : Fˣ) (n : ℕ)
    (hn : 0 < n) :
    GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J
      (n • J + principalDivisor f) where
  degree := n
  positive_degree := hn
  multiplier := f
  finite_incl v := by
    show (numberFieldGlobalPlaceData (F := F)).finiteDelta f v + n • J.finite v -
      (n • J + principalDivisor f).finite v ∈ (numberFieldFiniteLocalValueData v).cone
    rw [show (n • J + principalDivisor f).finite v =
        n • J.finite v + (numberFieldGlobalPlaceData (F := F)).finiteDelta f v from by
      simp [GlobalIdealFamily.add_finite, GlobalIdealFamily.nsmul_finite, principalDivisor]]
    have h0 : (numberFieldGlobalPlaceData (F := F)).finiteDelta f v + n • J.finite v -
        (n • J.finite v + (numberFieldGlobalPlaceData (F := F)).finiteDelta f v) = 0 := by
      abel
    rw [h0]
    exact (numberFieldFiniteLocalValueData v).cone.zero_mem
  infinite_incl w := by
    show (numberFieldGlobalPlaceData (F := F)).infiniteDelta f w + n • J.infinite w -
      (n • J + principalDivisor f).infinite w ∈ (numberFieldInfiniteLocalValueData w).cone
    rw [show (n • J + principalDivisor f).infinite w =
        n • J.infinite w + (numberFieldGlobalPlaceData (F := F)).infiniteDelta f w from by
      simp [GlobalIdealFamily.add_infinite, GlobalIdealFamily.nsmul_infinite, principalDivisor]]
    have h0 : (numberFieldGlobalPlaceData (F := F)).infiniteDelta f w + n • J.infinite w -
        (n • J.infinite w + (numberFieldGlobalPlaceData (F := F)).infiniteDelta f w) = 0 := by
      ring
    rw [h0]
    exact (numberFieldInfiniteLocalValueData w).cone.zero_mem

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
