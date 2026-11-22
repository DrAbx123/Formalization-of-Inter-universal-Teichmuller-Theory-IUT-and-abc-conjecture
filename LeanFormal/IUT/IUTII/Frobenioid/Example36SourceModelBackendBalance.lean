import LeanFormal.IUT.IUTII.Frobenioid.Example36GlobalIdealFamily
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelDivisor
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelBackend
import LeanFormal.IUT.IUTII.Frobenioid.Example36NumberFieldPlaceData
import Mathlib.Data.Finset.Lattice.Basic

/-!
# The backend divisor balance of a global-ideal-family morphism

Handoff H: for a morphism `h : Hom D J1 J2` of degree `n` and multiplier `f`,
with effective part `Z = div(f) + n delta(J1) - delta(J2)`, the arithmetic
divisors `d(J) = -delta(J)` satisfy

  n d(J1) + Z = d(J2) + div(f).

This file proves the identity in the backend explicit divisor group
`ExplicitDivisor F = (HeightOneSpectrum ->_0 Z) x (InfinitePlace -> R)`,
coordinatewise from `GlobalIdealFamily.Hom.balance_finite` and
`balance_infinite`; it also proves that for the actual number-field place data
the effective part is nonnegative in the backend cone sense.  The frozen
backend object/divisorClass dictionary is imported read-only.

Boundary: divisor-group coordinates and place data only; no source theta/q-pilot
claims.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open IsDedekindDomain NumberField
open scoped NumberField

universe u

variable {F : Type u} [Field F] [NumberField F]

namespace SourceModelBackendBalance

/-- Natural multiples commute with negation in a ring. -/
theorem nsmul_neg_ring {R : Type*} [Ring R] (n : ℕ) (a : R) :
    n • (-a) = -(n • a) := by
  rw [nsmul_eq_mul, nsmul_eq_mul, mul_neg]

/-- The finite support of the effective part `Z` of a morphism: the union of
the support of the principal divisor of the multiplier and of the supports of
the two ideal-family objects. -/
def effectivePartFiniteSupport (D : GlobalPlaceData F) (hD : D.HasFiniteSupport)
    {J₁ J₂ : GlobalIdealFamily F} (h : GlobalIdealFamily.Hom D J₁ J₂) :
    Finset (HeightOneSpectrum (𝓞 F)) := by
  classical
  exact (hD h.multiplier).toFinset ∪ J₁.finite.support ∪ J₂.finite.support

/-- Off the support of the effective part, its finite coordinate vanishes. -/
theorem effectiveFinite_eq_zero_of_not_mem (D : GlobalPlaceData F)
    (hD : D.HasFiniteSupport) {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom D J₁ J₂) {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ effectivePartFiniteSupport D hD h) :
    h.effectiveFinite v = 0 := by
  have hv' : (v ∉ (hD h.multiplier).toFinset ∧ v ∉ J₁.finite.support) ∧
      v ∉ J₂.finite.support := by
    simpa only [effectivePartFiniteSupport, Finset.mem_union, not_or] using hv
  have hf : D.finiteDelta h.multiplier v = 0 := by
    by_contra hne
    exact hv'.1.1 ((hD h.multiplier).mem_toFinset.mpr hne)
  have hJ₁ : J₁.finite v = 0 := by
    by_contra hne
    exact hv'.1.2 (Finsupp.mem_support_iff.mpr hne)
  have hJ₂ : J₂.finite v = 0 := by
    by_contra hne
    exact hv'.2 (Finsupp.mem_support_iff.mpr hne)
  unfold GlobalIdealFamily.Hom.effectiveFinite
  rw [hf, hJ₁, hJ₂, nsmul_zero, zero_add, sub_zero]

/-- The finite part of the effective divisor `Z` of a morphism. -/
def effectivePartFinite (D : GlobalPlaceData F) (hD : D.HasFiniteSupport)
    {J₁ J₂ : GlobalIdealFamily F} (h : GlobalIdealFamily.Hom D J₁ J₂) :
    HeightOneSpectrum (𝓞 F) →₀ ℤ :=
  Finsupp.onFinset (effectivePartFiniteSupport D hD h)
    (fun v => h.effectiveFinite v)
    (fun v hv => by
      by_contra hmem
      exact hv (effectiveFinite_eq_zero_of_not_mem D hD h hmem))

@[simp]
theorem effectivePartFinite_apply (D : GlobalPlaceData F) (hD : D.HasFiniteSupport)
    {J₁ J₂ : GlobalIdealFamily F} (h : GlobalIdealFamily.Hom D J₁ J₂)
    (v : HeightOneSpectrum (𝓞 F)) :
    effectivePartFinite D hD h v = h.effectiveFinite v :=
  Finsupp.onFinset_apply

/-- The effective part `Z` as an explicit backend divisor. -/
def effectiveDivisorOfHom (D : GlobalPlaceData F) (hD : D.HasFiniteSupport)
    {J₁ J₂ : GlobalIdealFamily F} (h : GlobalIdealFamily.Hom D J₁ J₂) :
    SourceModelBackend.ExplicitDivisor F :=
  (effectivePartFinite D hD h, fun w => h.effectiveInfinite w)

/-- The principal divisor `div(f)` of the multiplier in explicit coordinates,
using the principal map of `D`. -/
def principalDivisorOfPlaceData (D : GlobalPlaceData F) (hD : D.HasFiniteSupport)
    (f : Fˣ) : SourceModelBackend.ExplicitDivisor F :=
  ((sourceModelPrincipalDivisor D hD f).finite,
    fun w => (sourceModelPrincipalDivisor D hD f).infinite w)

@[simp]
theorem principalDivisorOfPlaceData_fst_apply (D : GlobalPlaceData F)
    (hD : D.HasFiniteSupport) (f : Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (principalDivisorOfPlaceData D hD f).1 v = D.finiteDelta f v := by
  simp [principalDivisorOfPlaceData, sourceModelPrincipalDivisor_finite_apply]

@[simp]
theorem principalDivisorOfPlaceData_snd_apply (D : GlobalPlaceData F)
    (hD : D.HasFiniteSupport) (f : Fˣ) (w : NumberField.InfinitePlace F) :
    (principalDivisorOfPlaceData D hD f).2 w = D.infiniteDelta f w := rfl

/-- **Backend divisor balance.**  For a morphism `h : Hom D J1 J2`,
`n d(J1) + Z = d(J2) + div(f)` in the explicit backend divisor group, where
`d(J) = -delta(J)` and `Z` is the effective part.  Proved coordinatewise from
`GlobalIdealFamily.Hom.balance_finite` and `balance_infinite`. -/
theorem backendBalanceEquation (D : GlobalPlaceData F) (hD : D.HasFiniteSupport)
    {J₁ J₂ : GlobalIdealFamily F} (h : GlobalIdealFamily.Hom D J₁ J₂) :
    h.degree • arithmeticDivisorExplicit J₁ + effectiveDivisorOfHom D hD h =
      arithmeticDivisorExplicit J₂ + principalDivisorOfPlaceData D hD h.multiplier := by
  apply Prod.ext
  · ext v
    change (h.degree • (arithmeticDivisorExplicit J₁).1 +
        effectivePartFinite D hD h) v =
      ((arithmeticDivisorExplicit J₂).1 +
        (sourceModelPrincipalDivisor D hD h.multiplier).finite) v
    rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.nsmul_apply,
      effectivePartFinite_apply]
    change h.degree • (-J₁.finite v) + h.effectiveFinite v =
      -J₂.finite v + D.finiteDelta h.multiplier v
    rw [nsmul_neg_ring]
    exact GlobalIdealFamily.Hom.balance_finite h v
  · funext w
    change (h.degree • (arithmeticDivisorExplicit J₁).2 +
        (fun w => h.effectiveInfinite w)) w =
      ((arithmeticDivisorExplicit J₂).2 +
        (sourceModelPrincipalDivisor D hD h.multiplier).infinite) w
    simp only [Pi.add_apply, Pi.smul_apply]
    change h.degree • (-J₁.infinite w) + h.effectiveInfinite w =
      -J₂.infinite w + D.infiniteDelta h.multiplier w
    rw [nsmul_neg_ring]
    exact GlobalIdealFamily.Hom.balance_infinite h w

/-- For the actual number-field place data, the effective part `Z` is
nonnegative in the backend explicit-divisor sense. -/
theorem numberFieldEffectiveDivisorOfHom_explicitNonneg
    {J₁ J₂ : GlobalIdealFamily F} (h : GlobalIdealFamily.Hom
      (numberFieldGlobalPlaceData (F := F)) J₁ J₂) :
    SourceModelBackend.explicitNonneg (F := F)
      (effectiveDivisorOfHom (numberFieldGlobalPlaceData (F := F))
        numberFieldGlobalPlaceData_hasFiniteSupport h) := by
  refine ⟨fun v => ?_, fun w => ?_⟩
  · show (0 : ℤ) ≤ effectivePartFinite (numberFieldGlobalPlaceData (F := F))
      numberFieldGlobalPlaceData_hasFiniteSupport h v
    rw [effectivePartFinite_apply]
    have hv := h.effectiveFinite_mem_cone v
    simpa [numberFieldGlobalPlaceData, numberFieldFiniteLocalValueData,
      integerNonnegCone] using hv
  · show (0 : ℝ) ≤ h.effectiveInfinite w
    have hw := h.effectiveInfinite_mem_cone w
    simpa [numberFieldGlobalPlaceData, numberFieldInfiniteLocalValueData,
      realNonnegCone] using hw

end SourceModelBackendBalance

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
