import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelDivisor
import LeanFormal.IUT.IUTII.Frobenioid.PrimeStripFrobenioidCategorySkeleton

/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-!
# Frobenius degree dynamics on the concrete value/divisor data of III Example 3.6

This module formalizes the value/divisor-side fragment of boundary item (4) of
the prime-strip Frobenioid skeleton: the Frobenius degree n dynamics

  x |-> x ^ n

on the global unit group F^x of a number field F, together with its action on
the value coordinates and principal divisors of Example 3.6.

Main contents:

1. Concrete local scaling laws.  At a finite place v the v-adic exponent
   scales as nu_v(f^n) = n * nu_v(f); at an archimedean place w the coordinate
   -log (w f) scales as -log (w (f^n)) = n * (-log (w f)).  The proofs reuse
   LocalValueData.deltaAdd_pow (through numberFieldFiniteLocalValueData and
   numberFieldInfiniteLocalValueData) and the global-place versions
   GlobalPlaceData.finiteDelta_pow and GlobalPlaceData.infiniteDelta_pow.
2. Principal-divisor scaling.  In the value coordinates of Example 3.6,

     principalDivisorFinite (f^n) = n . principalDivisorFinite f
     principalDivisorInfinite (f^n) = n * principalDivisorInfinite f
     div (f^n) = n . div f,

   and, in the backend coordinates of the Layer-4a/4b backend,
   SourceModelBackend.principalDivisorExplicit and
   SourceModelBackend.globalModelDivisor scale by the same factor n.
3. The effective cone is preserved by the Frobenius scaling n . (-):
   explicitNonneg of the explicit divisor group, the coordinatewise effective
   cone GlobalIdealFamily.IsEffective, and the effective part of a morphism of
   global ideal families at every place.
4. Frobenius scaling commutes with the principal-divisor translation
   J |-> J + div(f) up to the factor n:

     n . (J + div f) = n . J + div (f^n),

   in value coordinates and in the backend divisor coordinates, in the exact
   coordinate form used by GlobalIdealFamily.Hom.balance_finite /
   balance_infinite and by SourceModelBackend.backendBalanceEquation.
5. Connection with the prime-strip skeleton.  For each actual place, the
   coordinate map (finite: nu_v, archimedean: -log (w .)) is packaged as a
   FrobenioidValueKernel F^x through
   K1K2Realization.frobenioidValueKernelOfValueMap; the skeleton's degree and
   realification laws for valueFrobeniusPower then specialize to the concrete
   statements

     K.degree (valueFrobeniusPower n f) = (K.degree f)^n
     K.realification (valueFrobeniusPower n f) = n * K.realification f,

   with K.realification the actual place coordinate.

Sign conventions (frozen, not silently flipped).  The object coordinate of a
global ideal family is delta(J) = J; the backend divisor is d(J) = -delta(J);
the principal divisor div(f) has value coordinates nu_v(f) and -log (w f), and
the backend explicit divisor Div(f) uses those same +delta(f) coordinates.  The
balance identity reads n d(J1) + Z = d(J2) + Div(f).  All scaling statements
below are stated in these coordinates; the archimedean Frobenius statement
keeps the minus sign of -log (w f).

Boundary (honest): only the value/divisor side of boundary item (4) is treated
here.  The log-shell compatibility of the Frobenius dynamics and the source
Frobenius carrier for the log-shell layer are NOT constructed: they remain the
exact card recorded in the prime-strip skeleton audit note.  No theta-pilot,
q-pilot, Tate uniformization, Hodge-theater or source-identification claim is
made.  The only inputs are the concrete place data and divisor backend of
Example 3.6 and the skeleton's valueFrobeniusPower laws.
-/

noncomputable section

open scoped NumberField
open IsDedekindDomain NumberField

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

universe u

variable {F : Type u} [Field F] [NumberField F]

/-! ## 0. The coordinatewise effective cone of a global ideal family -/

namespace GlobalIdealFamily

/-- The coordinatewise effective cone of a global ideal family: at every finite
place the valuation exponent lies in the integral cone, and at every archimedean
place the -log coordinate is nonnegative. -/
def IsEffective (D : GlobalPlaceData F) (J : GlobalIdealFamily F) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 F), J.finite v ∈ (D.finiteValue v).cone) ∧
    (∀ w : NumberField.InfinitePlace F, J.infinite w ∈ (D.infiniteValue w).cone)

variable {D : GlobalPlaceData F} {J : GlobalIdealFamily F}

/-- The standard object lies in the effective cone. -/
theorem IsEffective.zero (D : GlobalPlaceData F) :
    (0 : GlobalIdealFamily F).IsEffective D := by
  refine ⟨fun v => ?_, fun w => ?_⟩
  · rw [GlobalIdealFamily.zero_finite]
    exact (D.finiteValue v).cone.zero_mem
  · rw [GlobalIdealFamily.zero_infinite]
    exact (D.infiniteValue w).cone.zero_mem

/-- The effective cone is closed under addition of ideal families. -/
theorem IsEffective.add {J₁ J₂ : GlobalIdealFamily F}
    (h₁ : J₁.IsEffective D) (h₂ : J₂.IsEffective D) :
    (J₁ + J₂).IsEffective D := by
  refine ⟨fun v => ?_, fun w => ?_⟩
  · rw [GlobalIdealFamily.add_finite, Finsupp.add_apply]
    exact (D.finiteValue v).cone.add_mem (h₁.1 v) (h₂.1 v)
  · rw [GlobalIdealFamily.add_infinite]
    exact (D.infiniteValue w).cone.add_mem (h₁.2 w) (h₂.2 w)

/-- The effective cone is preserved by natural multiples n . (-): this is the
nsmul_mem closure used by the Frobenius degree dynamics. -/
theorem IsEffective.nsmul (h : J.IsEffective D) (n : ℕ) :
    (n • J).IsEffective D := by
  refine ⟨fun v => ?_, fun w => ?_⟩
  · rw [GlobalIdealFamily.nsmul_finite, Finsupp.nsmul_apply]
    exact (D.finiteValue v).nsmul_mem_cone (h.1 v) n
  · rw [GlobalIdealFamily.nsmul_infinite]
    exact (D.infiniteValue w).nsmul_mem_cone (h.2 w) n

namespace Hom

/-- The effective part of a morphism of global ideal families, scaled by n, still
lies in the effective cone at a finite place: the coordinate form used by
GlobalIdealFamily.Hom.balance_finite. -/
theorem nsmul_effectiveFinite_mem_cone {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom D J₁ J₂) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    n • h.effectiveFinite v ∈ (D.finiteValue v).cone :=
  (D.finiteValue v).nsmul_mem_cone (h.effectiveFinite_mem_cone v) n

/-- The effective part of a morphism of global ideal families, scaled by n, still
lies in the effective cone at an archimedean place: the coordinate form used by
GlobalIdealFamily.Hom.balance_infinite. -/
theorem nsmul_effectiveInfinite_mem_cone {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom D J₁ J₂) (w : NumberField.InfinitePlace F) (n : ℕ) :
    n • h.effectiveInfinite w ∈ (D.infiniteValue w).cone :=
  (D.infiniteValue w).nsmul_mem_cone (h.effectiveInfinite_mem_cone w) n

end Hom

end GlobalIdealFamily

/-! ## 1. Concrete local and principal-divisor scaling laws -/

namespace FrobeniusValueAction

/-- Frobenius scaling of the finite-place v-adic exponent:
nu_v(f^n) = n * nu_v(f). -/
theorem finitePlaceValueExponent_pow (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) (n : ℕ) :
    finitePlaceValueExponent v (f ^ n) = n • finitePlaceValueExponent v f := by
  rw [← numberFieldFiniteLocalValueData_deltaAdd, ← numberFieldFiniteLocalValueData_deltaAdd]
  exact LocalValueData.deltaAdd_pow (numberFieldFiniteLocalValueData v) f n

/-- Frobenius scaling of the archimedean coordinate -log (w .):
-log (w (f^n)) = n * (-log (w f)), with the sign of the coordinate kept. -/
theorem archimedeanPlaceValue_pow (w : NumberField.InfinitePlace F) (f : Fˣ) (n : ℕ) :
    archimedeanPlaceValue w (f ^ n) = n • archimedeanPlaceValue w f := by
  rw [← numberFieldInfiniteLocalValueData_deltaAdd, ← numberFieldInfiniteLocalValueData_deltaAdd]
  exact LocalValueData.deltaAdd_pow (numberFieldInfiniteLocalValueData w) f n

/-- Realified form of the finite-place Frobenius law (the actual arithmetic
degree coordinate): nu_v(f^n) = n * nu_v(f) in Real. -/
theorem finitePlaceValueExponent_pow_realified (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ)
    (n : ℕ) :
    (finitePlaceValueExponent v (f ^ n) : ℝ) = (n : ℝ) * (finitePlaceValueExponent v f : ℝ) := by
  rw [finitePlaceValueExponent_pow, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]

/-- Realified form of the archimedean Frobenius law, with the frozen sign
convention -log (w .). -/
theorem archimedeanPlaceValue_pow_realified (w : NumberField.InfinitePlace F) (f : Fˣ)
    (n : ℕ) :
    archimedeanPlaceValue w (f ^ n) = (n : ℝ) * archimedeanPlaceValue w f := by
  rw [archimedeanPlaceValue_pow, nsmul_eq_mul]

/-- Frobenius scaling of the finite principal divisor:
principalDivisorFinite (f^n) = n . principalDivisorFinite f. -/
theorem principalDivisorFinite_pow (f : Fˣ) (n : ℕ) :
    principalDivisorFinite (f ^ n) = n • principalDivisorFinite f := by
  ext v
  rw [principalDivisorFinite_apply, Finsupp.nsmul_apply, principalDivisorFinite_apply,
    ← numberFieldGlobalPlaceData_finiteDelta, ← numberFieldGlobalPlaceData_finiteDelta]
  exact GlobalPlaceData.finiteDelta_pow (numberFieldGlobalPlaceData (F := F)) f n v

/-- Frobenius scaling of the archimedean principal function:
principalDivisorInfinite (f^n) = n * principalDivisorInfinite f. -/
theorem principalDivisorInfinite_pow (f : Fˣ) (n : ℕ) :
    principalDivisorInfinite (f ^ n) = n • principalDivisorInfinite f := by
  funext w
  rw [principalDivisorInfinite_apply, Pi.smul_apply, principalDivisorInfinite_apply,
    Units.val_pow_eq_pow_val, map_pow, Real.log_pow, nsmul_eq_mul]
  ring

/-- Frobenius scaling of the principal divisor in value coordinates:
div (f^n) = n . div f, for any place data with finite support. -/
theorem sourceModelPrincipalDivisor_pow (D : GlobalPlaceData F)
    (hD : D.HasFiniteSupport) (f : Fˣ) (n : ℕ) :
    sourceModelPrincipalDivisor D hD (f ^ n) = n • sourceModelPrincipalDivisor D hD f := by
  apply GlobalIdealFamily.ext
  · ext v
    rw [GlobalIdealFamily.nsmul_finite, Finsupp.nsmul_apply,
      sourceModelPrincipalDivisor_finite_apply, sourceModelPrincipalDivisor_finite_apply]
    exact GlobalPlaceData.finiteDelta_pow D f n v
  · funext w
    rw [GlobalIdealFamily.nsmul_infinite, sourceModelPrincipalDivisor_infinite_apply,
      sourceModelPrincipalDivisor_infinite_apply]
    exact GlobalPlaceData.infiniteDelta_pow D f n w

/-- Frobenius scaling of the principal divisor in the backend divisor
coordinates d = -delta: d (div (f^n)) = n . d (div f). -/
theorem arithmeticDivisor_sourceModelPrincipalDivisor_pow (D : GlobalPlaceData F)
    (hD : D.HasFiniteSupport) (f : Fˣ) (n : ℕ) :
    arithmeticDivisor (sourceModelPrincipalDivisor D hD (f ^ n)) =
      n • arithmeticDivisor (sourceModelPrincipalDivisor D hD f) := by
  rw [sourceModelPrincipalDivisor_pow, arithmeticDivisor_nsmul]

/-- Frobenius scaling of the explicit backend principal divisor
Div(f) = (nu_v(f), -log (w f)): it scales by the factor n. -/
theorem sourceModelBackendPrincipalDivisorExplicit_pow (f : Fˣ) (n : ℕ) :
    SourceModelBackend.principalDivisorExplicit (Additive.ofMul (f ^ n)) =
      n • SourceModelBackend.principalDivisorExplicit (Additive.ofMul f) := by
  rw [ofMul_pow, map_nsmul]

/-- Frobenius scaling of the backend principal divisor in the Grothendieck group
of the effective cone attaches the same factor n. -/
theorem sourceModelBackendGlobalModelDivisor_pow (f : Fˣ) (n : ℕ) :
    SourceModelBackend.globalModelDivisor (Additive.ofMul (f ^ n)) =
      n • SourceModelBackend.globalModelDivisor (Additive.ofMul f) := by
  rw [ofMul_pow, map_nsmul]

/-! ## 2. The Frobenius endomorphism and the divisor laws -/

/-- The skeleton's Frobenius power endomorphism valueFrobeniusPower n scales the
finite principal divisor by n. -/
theorem principalDivisorFinite_valueFrobeniusPower (f : Fˣ) (n : ℕ+) :
    principalDivisorFinite (valueFrobeniusPower n f) =
      (n : ℕ) • principalDivisorFinite f := by
  rw [valueFrobeniusPower_apply, principalDivisorFinite_pow]

/-- The skeleton's Frobenius power endomorphism scales the archimedean principal
function by n. -/
theorem principalDivisorInfinite_valueFrobeniusPower (f : Fˣ) (n : ℕ+) :
    principalDivisorInfinite (valueFrobeniusPower n f) =
      (n : ℕ) • principalDivisorInfinite f := by
  rw [valueFrobeniusPower_apply, principalDivisorInfinite_pow]

/-- The skeleton's Frobenius power endomorphism scales the principal divisor div
by n, in value coordinates. -/
theorem sourceModelPrincipalDivisor_valueFrobeniusPower (D : GlobalPlaceData F)
    (hD : D.HasFiniteSupport) (f : Fˣ) (n : ℕ+) :
    sourceModelPrincipalDivisor D hD (valueFrobeniusPower n f) =
      (n : ℕ) • sourceModelPrincipalDivisor D hD f := by
  rw [valueFrobeniusPower_apply, sourceModelPrincipalDivisor_pow]

/-- The skeleton's Frobenius power endomorphism scales the explicit backend
principal divisor by n. -/
theorem sourceModelBackendPrincipalDivisorExplicit_valueFrobeniusPower (f : Fˣ)
    (n : ℕ+) :
    SourceModelBackend.principalDivisorExplicit
        (Additive.ofMul (valueFrobeniusPower n f)) =
      (n : ℕ) • SourceModelBackend.principalDivisorExplicit (Additive.ofMul f) := by
  rw [valueFrobeniusPower_apply, sourceModelBackendPrincipalDivisorExplicit_pow]

/-! ## 3. The effective cone under Frobenius scaling -/

/-- The nonnegativity cone of the explicit backend divisor group is preserved by
natural multiples: the nsmul_mem closure of the effective cone. -/
theorem explicitNonneg_nsmul (n : ℕ) {v : SourceModelBackend.ExplicitDivisor F}
    (h : SourceModelBackend.explicitNonneg v) :
    SourceModelBackend.explicitNonneg (n • v) := by
  refine ⟨fun s => ?_, fun w => ?_⟩
  · rw [Prod.smul_fst, Finsupp.nsmul_apply]
    exact nsmul_nonneg (h.1 s) n
  · rw [Prod.smul_snd, Pi.smul_apply]
    exact nsmul_nonneg (h.2 w) n

/-! ## 4. Frobenius scaling and the principal-divisor translation

The translation J |-> J + div(f) is compatible with the Frobenius scaling
n . (-) up to the factor n: the principal divisor of f^n compensates the factor
n.  These are the exact coordinate shapes used by the balance identities
GlobalIdealFamily.Hom.balance_finite / balance_infinite and by
SourceModelBackend.backendBalanceEquation. -/

/-- Frobenius scaling commutes with principal-divisor translation:
n . (J + div f) = n . J + div (f^n). -/
theorem nsmul_add_sourceModelPrincipalDivisor (D : GlobalPlaceData F)
    (hD : D.HasFiniteSupport) (n : ℕ) (J : GlobalIdealFamily F) (f : Fˣ) :
    n • (J + sourceModelPrincipalDivisor D hD f) =
      n • J + sourceModelPrincipalDivisor D hD (f ^ n) := by
  apply GlobalIdealFamily.ext
  · ext v
    have hl : (n • (J + sourceModelPrincipalDivisor D hD f)).finite v =
        n • J.finite v + n • D.finiteDelta f v := by
      rw [GlobalIdealFamily.nsmul_finite, Finsupp.nsmul_apply,
        GlobalIdealFamily.add_finite, Finsupp.add_apply,
        sourceModelPrincipalDivisor_finite_apply, nsmul_add]
    have hr : (n • J + sourceModelPrincipalDivisor D hD (f ^ n)).finite v =
        n • J.finite v + D.finiteDelta (f ^ n) v := by
      rw [GlobalIdealFamily.add_finite, Finsupp.add_apply,
        GlobalIdealFamily.nsmul_finite, Finsupp.nsmul_apply,
        sourceModelPrincipalDivisor_finite_apply]
    rw [hl, hr, GlobalPlaceData.finiteDelta_pow]
  · funext w
    have hl : (n • (J + sourceModelPrincipalDivisor D hD f)).infinite w =
        n • J.infinite w + n • D.infiniteDelta f w := by
      rw [GlobalIdealFamily.nsmul_infinite, GlobalIdealFamily.add_infinite,
        sourceModelPrincipalDivisor_infinite_apply, nsmul_add]
    have hr : (n • J + sourceModelPrincipalDivisor D hD (f ^ n)).infinite w =
        n • J.infinite w + D.infiniteDelta (f ^ n) w := by
      rw [GlobalIdealFamily.add_infinite, GlobalIdealFamily.nsmul_infinite,
        sourceModelPrincipalDivisor_infinite_apply]
    rw [hl, hr, GlobalPlaceData.infiniteDelta_pow]

/-- Coordinate form of the translation compatibility at a finite place, in the
shape of GlobalIdealFamily.Hom.balance_finite. -/
theorem nsmul_add_sourceModelPrincipalDivisor_finite (D : GlobalPlaceData F)
    (hD : D.HasFiniteSupport) (n : ℕ) (J : GlobalIdealFamily F) (f : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    (n • (J + sourceModelPrincipalDivisor D hD f)).finite v =
      n • J.finite v + n • D.finiteDelta f v := by
  rw [GlobalIdealFamily.nsmul_finite, Finsupp.nsmul_apply, GlobalIdealFamily.add_finite,
    Finsupp.add_apply, sourceModelPrincipalDivisor_finite_apply, nsmul_add]

/-- Coordinate form of the translation compatibility at an archimedean place, in
the shape of GlobalIdealFamily.Hom.balance_infinite. -/
theorem nsmul_add_sourceModelPrincipalDivisor_infinite (D : GlobalPlaceData F)
    (hD : D.HasFiniteSupport) (n : ℕ) (J : GlobalIdealFamily F) (f : Fˣ)
    (w : NumberField.InfinitePlace F) :
    (n • (J + sourceModelPrincipalDivisor D hD f)).infinite w =
      n • J.infinite w + n • D.infiniteDelta f w := by
  rw [GlobalIdealFamily.nsmul_infinite, GlobalIdealFamily.add_infinite,
    sourceModelPrincipalDivisor_infinite_apply, nsmul_add]

/-- Backend form of the translation compatibility: after applying the backend
divisor d = -delta, the scaled translated object is n . d J plus the arithmetic
divisor of div (f^n). -/
theorem arithmeticDivisor_nsmul_add_sourceModelPrincipalDivisor (D : GlobalPlaceData F)
    (hD : D.HasFiniteSupport) (n : ℕ) (J : GlobalIdealFamily F) (f : Fˣ) :
    arithmeticDivisor (n • (J + sourceModelPrincipalDivisor D hD f)) =
      n • arithmeticDivisor J +
        arithmeticDivisor (sourceModelPrincipalDivisor D hD (f ^ n)) := by
  rw [nsmul_add_sourceModelPrincipalDivisor, arithmeticDivisor_add, arithmeticDivisor_nsmul,
    arithmeticDivisor_sourceModelPrincipalDivisor_pow]

/-! ## 5. Value kernels and the skeleton's degree/realification laws -/

/-- The finite-place value kernel of the Frobenius dynamics: the value map
f |-> nu_v(f) on F^x packaged as a FrobenioidValueKernel of the prime-strip
skeleton. -/
noncomputable def finitePlaceValueKernel (D : GlobalPlaceData F)
    (v : HeightOneSpectrum (𝓞 F)) : FrobenioidValueKernel Fˣ :=
  K1K2Realization.frobenioidValueKernelOfValueMap
    (fun f : Fˣ => (D.finiteDelta f v : ℝ))
    (fun x y => by
      rw [GlobalPlaceData.finiteDelta_mul]
      push_cast
      ring)
    (by rw [GlobalPlaceData.finiteDelta_one]; norm_num)
    (fun f => f) (fun _ => rfl)

/-- The realification of the finite-place value kernel is the finite-place
coordinate nu_v. -/
theorem finitePlaceValueKernel_realification (D : GlobalPlaceData F)
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (finitePlaceValueKernel D v).realification f = (D.finiteDelta f v : ℝ) := rfl

/-- Skeleton degree law in the actual finite-place coordinates:
K.degree (valueFrobeniusPower n f) = (K.degree f)^n. -/
theorem finitePlaceValueKernel_valueFrobenius_degree (D : GlobalPlaceData F)
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) (n : ℕ+) :
    (finitePlaceValueKernel D v).degree (valueFrobeniusPower n f) =
      ((finitePlaceValueKernel D v).degree f) ^ (n : ℕ) :=
  valueFrobeniusPower_degree (finitePlaceValueKernel D v) n f

/-- Skeleton realification law in the actual finite-place coordinates:
K.realification (valueFrobeniusPower n f) = n * K.realification f, i.e. nu_v of
the Frobenius power is n times nu_v. -/
theorem finitePlaceValueKernel_valueFrobenius_realification (D : GlobalPlaceData F)
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) (n : ℕ+) :
    (finitePlaceValueKernel D v).realification (valueFrobeniusPower n f) =
      ((n : ℕ) : ℝ) * (D.finiteDelta f v : ℝ) := by
  rw [valueFrobeniusPower_apply, valueFrobeniusPower_realification,
    finitePlaceValueKernel_realification]

/-- The archimedean-place value kernel of the Frobenius dynamics: the value map
f |-> -log (w f) on F^x packaged as a FrobenioidValueKernel. -/
noncomputable def archimedeanPlaceValueKernel (D : GlobalPlaceData F)
    (w : NumberField.InfinitePlace F) : FrobenioidValueKernel Fˣ :=
  K1K2Realization.frobenioidValueKernelOfValueMap
    (fun f : Fˣ => D.infiniteDelta f w)
    (fun x y => by rw [GlobalPlaceData.infiniteDelta_mul])
    (by rw [GlobalPlaceData.infiniteDelta_one])
    (fun f => f) (fun _ => rfl)

/-- The realification of the archimedean-place value kernel is the archimedean
coordinate -log (w .). -/
theorem archimedeanPlaceValueKernel_realification (D : GlobalPlaceData F)
    (w : NumberField.InfinitePlace F) (f : Fˣ) :
    (archimedeanPlaceValueKernel D w).realification f = D.infiniteDelta f w := rfl

/-- Skeleton degree law in the actual archimedean coordinates. -/
theorem archimedeanPlaceValueKernel_valueFrobenius_degree (D : GlobalPlaceData F)
    (w : NumberField.InfinitePlace F) (f : Fˣ) (n : ℕ+) :
    (archimedeanPlaceValueKernel D w).degree (valueFrobeniusPower n f) =
      ((archimedeanPlaceValueKernel D w).degree f) ^ (n : ℕ) :=
  valueFrobeniusPower_degree (archimedeanPlaceValueKernel D w) n f

/-- Skeleton realification law in the actual archimedean coordinates:
K.realification (valueFrobeniusPower n f) = n * K.realification f, with
K.realification = -log (w .) and the minus sign kept. -/
theorem archimedeanPlaceValueKernel_valueFrobenius_realification (D : GlobalPlaceData F)
    (w : NumberField.InfinitePlace F) (f : Fˣ) (n : ℕ+) :
    (archimedeanPlaceValueKernel D w).realification (valueFrobeniusPower n f) =
      ((n : ℕ) : ℝ) * D.infiniteDelta f w := by
  rw [valueFrobeniusPower_apply, valueFrobeniusPower_realification,
    archimedeanPlaceValueKernel_realification]

/-- The concrete number-field finite-place kernel realification law:
nu_v (f^n) = n * nu_v (f), as an instance of the skeleton's degree dynamics. -/
theorem numberFieldFiniteValueKernel_valueFrobenius_realification
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) (n : ℕ+) :
    (finitePlaceValueKernel (numberFieldGlobalPlaceData (F := F)) v).realification
        (valueFrobeniusPower n f) =
      ((n : ℕ) : ℝ) * (finitePlaceValueExponent v f : ℝ) := by
  rw [finitePlaceValueKernel_valueFrobenius_realification,
    numberFieldGlobalPlaceData_finiteDelta]

/-- The concrete number-field archimedean kernel realification law:
-log (w (f^n)) = n * (-log (w f)), with the sign convention of
principalDivisorInfinite. -/
theorem numberFieldArchimedeanValueKernel_valueFrobenius_realification
    (w : NumberField.InfinitePlace F) (f : Fˣ) (n : ℕ+) :
    (archimedeanPlaceValueKernel (numberFieldGlobalPlaceData (F := F)) w).realification
        (valueFrobeniusPower n f) =
      ((n : ℕ) : ℝ) * principalDivisorInfinite f w := by
  rw [archimedeanPlaceValueKernel_valueFrobenius_realification,
    numberFieldGlobalPlaceData_infiniteDelta, principalDivisorInfinite_apply]

end FrobeniusValueAction

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
