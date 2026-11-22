import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelDivisor
import LeanFormal.IUT.IUTII.Frobenioid.PrimeStripFrobenioidCategorySkeleton

set_option linter.unusedSectionVars false

/-!
# Actual `V_K`/`rho_v` value maps from the number-field place data

Boundary item (2), value-map/rho_v fragment.  This module instantiates the
K1/K2 value-map entry `K1K2Realization.frobenioidValueKernelOfValueMap` and the
link-layer entry `K1K2Realization.primeStripFrobenioidLinkLayerOfValueMaps`
with the *actual* number-field place data of
`Example36NumberFieldPlaceData` / `Example36GlobalPlaceData`, and with the
actual `rho_v`-coordinates used by the Layer-4 backend of handoff
chapter 1, H-I (`Example36SourceModelBackend`, `Example36SourceModelDivisor`).

## The value maps

At a finite place `v` the backend uses the signed valuation coordinate
`nu_v(f) = D.finiteDelta f v` (the efficient/arithmetic-divisor coordinate of
`principalDivisorFinite`).  At an archimedean place `w` the coordinate is
`-log (w f) = D.infiniteDelta f w` (the `-log` of the archimedean absolute
value).  The actual number-field instantiation is

* `finiteValueMap numberFieldGlobalPlaceData v f = (nu_v(f) : Real)`,
  equal to `(finitePlaceValueExponent v f : Real)` and to the backend
  coordinate `(principalDivisorFinite f v : Real)`;
* `infiniteValueMap numberFieldGlobalPlaceData w f = -log (w f)`, equal to
  `principalDivisorInfinite f w`.

Both are additive over multiplication and vanish at `1` (from the
multiplicativity and unit laws of the global place data), so each determines a
reduced Frobenioid value kernel by the K1/K2 entry.

## Contents

1. `finiteValueMap`, `infiniteValueMap`, the unified `placeValueMap`, their
   addition/unit laws, and their evaluation in the actual number-field and
   backend coordinates.
2. `finiteValueKernel`, `infiniteValueKernel`, `placeValueKernel`: the
   K1/K2 Frobenioid value kernels of the actual value maps (identity transport),
   with the degree/realification readback, unit and multiplication laws, power
   law, and the identification of the realification with the backend principal
   divisor coordinates.
3. `faithfulFiniteValueLink` and `faithfulInfiniteValueLink`: for two place
   data linked by a `FaithfulDomainIsomorphism` (a genuine field ring
   equivalence plus place maps preserving the local value coordinates), the K1/K2
   link layer built from the two actual value maps, with the localFrobenioid
   degree readback and the mod/MOD realification compatibility in actual
   coordinates.  The identity-place comparison is the special case
   `FaithfulDomainIsomorphism.identity`.
4. Range/image statements: the identifications `v((Qp)^x) = Q` and the degree
   image `Q * log p` are range statements on the value map.  They are *not*
   proved from the Frobenioid value-kernel or link-layer laws; they are exposed
   as the named hypotheses `FiniteValueMapRationalImage`,
   `InfiniteValueMapRationalImage`, `PlaceValueMapRationalImage` (reusing
   `K1K2Realization.ValueMapRationalImage`), together with their exact
   consequences (scaled rational image, kernel degree range).  The separation
   witness `zeroValueMapKernel_not_rationalImage` of the K1/K2 entry shows that
   no kernel field constrains the range.

## Boundary

This is the value-map/link-layer fragment of boundary (2) only.  It is not a
construction of the actual `V_K` transport at the prime-strip layer, not a
vertical log-Kummer construction, not a geometric `pi_1` statement, and not a
theta-pilot/Tate statement.  The completion carrier and the ring/place transport
used here are the Layer-2/Layer-4 abstractions; no claim is made that they
identify with the source Frobenius carrier of the log-shell layer.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open scoped NumberField
open IsDedekindDomain NumberField

universe u

variable {F : Type u} [Field F] [NumberField F]

/-! ## 1. The actual value maps `rho_v` at finite and archimedean places -/

/-- `rho_v` at a finite place: the backend signed valuation coordinate
`nu_v(f)`, cast to `Real` (the arithmetic-divisor/principal-divisor
coordinate of the place). -/
def finiteValueMap (D : GlobalPlaceData F) (v : HeightOneSpectrum (𝓞 F)) :
    Fˣ → ℝ :=
  fun f => (D.finiteDelta f v : ℝ)

/-- `rho_v` at an archimedean place: `-log` of the archimedean absolute value,
i.e. the local archimedean value coordinate `D.infiniteDelta f w`. -/
def infiniteValueMap (D : GlobalPlaceData F) (w : NumberField.InfinitePlace F) :
    Fˣ → ℝ :=
  fun f => D.infiniteDelta f w

/-- Evaluation of the finite value map. -/
@[simp]
theorem finiteValueMap_apply (D : GlobalPlaceData F) (v : HeightOneSpectrum (𝓞 F))
    (f : Fˣ) :
    finiteValueMap D v f = (D.finiteDelta f v : ℝ) :=
  rfl

/-- Evaluation of the archimedean value map. -/
@[simp]
theorem infiniteValueMap_apply (D : GlobalPlaceData F)
    (w : NumberField.InfinitePlace F) (f : Fˣ) :
    infiniteValueMap D w f = D.infiniteDelta f w :=
  rfl

/-- The finite value map is the additive form of the local value data at the
place. -/
theorem finiteValueMap_eq_deltaAdd (D : GlobalPlaceData F)
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    finiteValueMap D v f = ((D.finiteValue v).deltaAdd f : ℝ) :=
  rfl

/-- The archimedean value map is the additive form of the archimedean local
value data. -/
theorem infiniteValueMap_eq_deltaAdd (D : GlobalPlaceData F)
    (w : NumberField.InfinitePlace F) (f : Fˣ) :
    infiniteValueMap D w f = (D.infiniteValue w).deltaAdd f :=
  rfl

/-- At an actual number-field finite place, the finite value map is the
`v`-adic exponent `nu_v(f)` (in `Real`). -/
theorem finiteValueMap_numberField (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    finiteValueMap (numberFieldGlobalPlaceData (F := F)) v f =
      (finitePlaceValueExponent v f : ℝ) := by
  rw [finiteValueMap_apply, numberFieldGlobalPlaceData_finiteDelta]

/-- At an actual number-field archimedean place, the value map is
`-log` of the archimedean absolute value. -/
theorem infiniteValueMap_numberField (w : NumberField.InfinitePlace F) (f : Fˣ) :
    infiniteValueMap (numberFieldGlobalPlaceData (F := F)) w f =
      -Real.log (w (f : F)) := by
  rw [infiniteValueMap_apply, numberFieldGlobalPlaceData_infiniteDelta]

/-- The actual finite value map is the backend principal-divisor coordinate
`principalDivisorFinite`. -/
theorem finiteValueMap_eq_principalDivisorFinite (v : HeightOneSpectrum (𝓞 F))
    (f : Fˣ) :
    finiteValueMap (numberFieldGlobalPlaceData (F := F)) v f =
      (principalDivisorFinite f v : ℝ) := by
  rw [finiteValueMap_numberField, principalDivisorFinite_apply]

/-- The actual archimedean value map is the backend principal-divisor coordinate
`principalDivisorInfinite`. -/
theorem infiniteValueMap_eq_principalDivisorInfinite
    (w : NumberField.InfinitePlace F) (f : Fˣ) :
    infiniteValueMap (numberFieldGlobalPlaceData (F := F)) w f =
      principalDivisorInfinite f w := by
  rw [infiniteValueMap_numberField, principalDivisorInfinite_apply]

/-- The actual finite value map is the first coordinate of the backend explicit
principal divisor. -/
theorem finiteValueMap_eq_principalDivisorExplicit_fst
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    finiteValueMap (numberFieldGlobalPlaceData (F := F)) v f =
      ((principalDivisorExplicit f).1 v : ℝ) := by
  rw [finiteValueMap_eq_principalDivisorFinite]
  rfl

/-- The actual archimedean value map is the second coordinate of the backend
explicit principal divisor. -/
theorem infiniteValueMap_eq_principalDivisorExplicit_snd
    (w : NumberField.InfinitePlace F) (f : Fˣ) :
    infiniteValueMap (numberFieldGlobalPlaceData (F := F)) w f =
      (principalDivisorExplicit f).2 w := by
  rw [infiniteValueMap_eq_principalDivisorInfinite]
  rfl

/-- The finite value map is additive (the `v`-adic exponent is multiplicative
under units). -/
theorem finiteValueMap_mul (D : GlobalPlaceData F) (v : HeightOneSpectrum (𝓞 F))
    (f g : Fˣ) :
    finiteValueMap D v (f * g) = finiteValueMap D v f + finiteValueMap D v g := by
  rw [finiteValueMap_apply, finiteValueMap_apply, finiteValueMap_apply,
    GlobalPlaceData.finiteDelta_mul]
  push_cast
  ring

/-- The finite value map vanishes at `1`. -/
@[simp]
theorem finiteValueMap_one (D : GlobalPlaceData F) (v : HeightOneSpectrum (𝓞 F)) :
    finiteValueMap D v 1 = 0 := by
  rw [finiteValueMap_apply, GlobalPlaceData.finiteDelta_one]
  norm_num

/-- The archimedean value map is additive. -/
theorem infiniteValueMap_mul (D : GlobalPlaceData F)
    (w : NumberField.InfinitePlace F) (f g : Fˣ) :
    infiniteValueMap D w (f * g) =
      infiniteValueMap D w f + infiniteValueMap D w g := by
  rw [infiniteValueMap_apply, infiniteValueMap_apply, infiniteValueMap_apply,
    GlobalPlaceData.infiniteDelta_mul]

/-- The archimedean value map vanishes at `1`. -/
@[simp]
theorem infiniteValueMap_one (D : GlobalPlaceData F)
    (w : NumberField.InfinitePlace F) :
    infiniteValueMap D w 1 = 0 := by
  rw [infiniteValueMap_apply, GlobalPlaceData.infiniteDelta_one]

/-- A place of the number field for the value-map fragment: a finite place or an
archimedean place. -/
abbrev ValuePlace (F : Type u) [Field F] [NumberField F] : Type u :=
  HeightOneSpectrum (𝓞 F) ⊕ NumberField.InfinitePlace F

/-- The value map `rho_v` at every place, unified over finite and archimedean
places. -/
def placeValueMap (D : GlobalPlaceData F) : ValuePlace F → Fˣ → ℝ
  | Sum.inl v => finiteValueMap D v
  | Sum.inr w => infiniteValueMap D w

/-- The unified value map at a finite place is the finite value map. -/
@[simp]
theorem placeValueMap_finite (D : GlobalPlaceData F) (v : HeightOneSpectrum (𝓞 F)) :
    placeValueMap D (Sum.inl v) = finiteValueMap D v :=
  rfl

/-- The unified value map at an archimedean place is the archimedean value map. -/
@[simp]
theorem placeValueMap_infinite (D : GlobalPlaceData F)
    (w : NumberField.InfinitePlace F) :
    placeValueMap D (Sum.inr w) = infiniteValueMap D w :=
  rfl

/-- The unified value map is additive at every place. -/
theorem placeValueMap_mul (D : GlobalPlaceData F) (place : ValuePlace F) (f g : Fˣ) :
    placeValueMap D place (f * g) = placeValueMap D place f + placeValueMap D place g := by
  rcases place with v | w
  · exact finiteValueMap_mul D v f g
  · exact infiniteValueMap_mul D w f g

/-- The unified value map vanishes at `1` at every place. -/
theorem placeValueMap_one (D : GlobalPlaceData F) (place : ValuePlace F) :
    placeValueMap D place 1 = 0 := by
  rcases place with v | w
  · exact finiteValueMap_one D v
  · exact infiniteValueMap_one D w


/-! ## 2. The K1/K2 value kernels of the actual value maps -/

section ValueKernels

variable (D : GlobalPlaceData F)

/-- The reduced Frobenioid value kernel of the actual finite-place value map,
by the K1/K2 value-map entry (with identity transport). -/
def finiteValueKernel (v : HeightOneSpectrum (𝓞 F)) : FrobenioidValueKernel Fˣ :=
  LeanFormal.IUT.K1K2Realization.frobenioidValueKernelOfValueMap
    (finiteValueMap D v) (fun f g => finiteValueMap_mul D v f g)
    (finiteValueMap_one D v) id (fun _ => rfl)

/-- The reduced Frobenioid value kernel of the actual archimedean value map. -/
def infiniteValueKernel (w : NumberField.InfinitePlace F) :
    FrobenioidValueKernel Fˣ :=
  LeanFormal.IUT.K1K2Realization.frobenioidValueKernelOfValueMap
    (infiniteValueMap D w) (fun f g => infiniteValueMap_mul D w f g)
    (infiniteValueMap_one D w) id (fun _ => rfl)

/-- The reduced Frobenioid value kernel of the unified value map at a place. -/
def placeValueKernel (place : ValuePlace F) : FrobenioidValueKernel Fˣ :=
  LeanFormal.IUT.K1K2Realization.frobenioidValueKernelOfValueMap
    (placeValueMap D place) (fun f g => placeValueMap_mul D place f g)
    (placeValueMap_one D place) id (fun _ => rfl)

/-- The realification of the finite value kernel is the actual finite value
map, definitionally (K1/K2 entry). -/
theorem finiteValueKernel_realification (v : HeightOneSpectrum (𝓞 F)) :
    (finiteValueKernel D v).realification = finiteValueMap D v :=
  LeanFormal.IUT.K1K2Realization.frobenioidValueKernelOfValueMap_realification
    (finiteValueMap D v) (fun f g => finiteValueMap_mul D v f g)
    (finiteValueMap_one D v) id (fun _ => rfl)

/-- The realification of the archimedean value kernel is the actual
archimedean value map. -/
theorem infiniteValueKernel_realification (w : NumberField.InfinitePlace F) :
    (infiniteValueKernel D w).realification = infiniteValueMap D w :=
  LeanFormal.IUT.K1K2Realization.frobenioidValueKernelOfValueMap_realification
    (infiniteValueMap D w) (fun f g => infiniteValueMap_mul D w f g)
    (infiniteValueMap_one D w) id (fun _ => rfl)

/-- The realification of the unified value kernel is the unified value map. -/
theorem placeValueKernel_realification (place : ValuePlace F) :
    (placeValueKernel D place).realification = placeValueMap D place :=
  LeanFormal.IUT.K1K2Realization.frobenioidValueKernelOfValueMap_realification
    (placeValueMap D place) (fun f g => placeValueMap_mul D place f g)
    (placeValueMap_one D place) id (fun _ => rfl)

/-- Evaluation of the finite value-kernel realification in actual coordinates. -/
@[simp]
theorem finiteValueKernel_realification_apply (v : HeightOneSpectrum (𝓞 F))
    (f : Fˣ) :
    (finiteValueKernel D v).realification f = (D.finiteDelta f v : ℝ) :=
  rfl

/-- Evaluation of the archimedean value-kernel realification in actual
coordinates. -/
@[simp]
theorem infiniteValueKernel_realification_apply (w : NumberField.InfinitePlace F)
    (f : Fˣ) :
    (infiniteValueKernel D w).realification f = D.infiniteDelta f w :=
  rfl

/-- Evaluation of the unified value-kernel realification. -/
@[simp]
theorem placeValueKernel_realification_apply (place : ValuePlace F) (f : Fˣ) :
    (placeValueKernel D place).realification f = placeValueMap D place f :=
  rfl

/-- The degree of the finite value kernel is `Multiplicative.ofAdd` of the
actual finite value. -/
@[simp]
theorem finiteValueKernel_degree_apply (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (finiteValueKernel D v).degree f =
      Multiplicative.ofAdd ((D.finiteDelta f v : ℝ)) :=
  rfl

/-- The degree of the archimedean value kernel is `Multiplicative.ofAdd` of
the actual archimedean value. -/
@[simp]
theorem infiniteValueKernel_degree_apply (w : NumberField.InfinitePlace F)
    (f : Fˣ) :
    (infiniteValueKernel D w).degree f =
      Multiplicative.ofAdd (D.infiniteDelta f w) :=
  rfl

/-- The real degree of the finite value kernel is the actual finite value. -/
theorem finiteValueKernel_degree_coe (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    ((finiteValueKernel D v).degree f : ℝ) = (D.finiteDelta f v : ℝ) :=
  LeanFormal.IUT.K1K2Realization.frobenioidValueKernelOfValueMap_degree_coe
    (finiteValueMap D v) (fun f g => finiteValueMap_mul D v f g)
    (finiteValueMap_one D v) id (fun _ => rfl) f

/-- The real degree of the archimedean value kernel is the actual archimedean
value. -/
theorem infiniteValueKernel_degree_coe (w : NumberField.InfinitePlace F) (f : Fˣ) :
    ((infiniteValueKernel D w).degree f : ℝ) = D.infiniteDelta f w :=
  LeanFormal.IUT.K1K2Realization.frobenioidValueKernelOfValueMap_degree_coe
    (infiniteValueMap D w) (fun f g => infiniteValueMap_mul D w f g)
    (infiniteValueMap_one D w) id (fun _ => rfl) f

/-- The unit of the finite value kernel is `1`. -/
@[simp]
theorem finiteValueKernel_unit (v : HeightOneSpectrum (𝓞 F)) :
    (finiteValueKernel D v).unit = 1 :=
  rfl

/-- The unit of the archimedean value kernel is `1`. -/
@[simp]
theorem infiniteValueKernel_unit (w : NumberField.InfinitePlace F) :
    (infiniteValueKernel D w).unit = 1 :=
  rfl

/-- The value-kernel unit law at a finite place, in actual coordinates. -/
theorem finiteValueKernel_unit_realification (v : HeightOneSpectrum (𝓞 F)) :
    (finiteValueKernel D v).realification (finiteValueKernel D v).unit = 0 :=
  FrobenioidValueKernel.realification_one _

/-- The value-kernel unit law at an archimedean place, in actual coordinates. -/
theorem infiniteValueKernel_unit_realification (w : NumberField.InfinitePlace F) :
    (infiniteValueKernel D w).realification (infiniteValueKernel D w).unit = 0 :=
  FrobenioidValueKernel.realification_one _

/-- The multiplication law of the finite value kernel in actual coordinates. -/
theorem finiteValueKernel_realification_mul (v : HeightOneSpectrum (𝓞 F))
    (f g : Fˣ) :
    (finiteValueKernel D v).realification (f * g) =
      (finiteValueKernel D v).realification f +
        (finiteValueKernel D v).realification g :=
  FrobenioidValueKernel.realification_mul _ f g

/-- The multiplication law of the archimedean value kernel in actual
coordinates. -/
theorem infiniteValueKernel_realification_mul (w : NumberField.InfinitePlace F)
    (f g : Fˣ) :
    (infiniteValueKernel D w).realification (f * g) =
      (infiniteValueKernel D w).realification f +
        (infiniteValueKernel D w).realification g :=
  FrobenioidValueKernel.realification_mul _ f g

/-- The degree multiplication law of the finite value kernel. -/
theorem finiteValueKernel_degree_mul (v : HeightOneSpectrum (𝓞 F)) (f g : Fˣ) :
    (finiteValueKernel D v).degree (f * g) =
      (finiteValueKernel D v).degree f * (finiteValueKernel D v).degree g :=
  FrobenioidValueKernel.degree_mul _ f g

/-- The degree multiplication law of the archimedean value kernel. -/
theorem infiniteValueKernel_degree_mul (w : NumberField.InfinitePlace F) (f g : Fˣ) :
    (infiniteValueKernel D w).degree (f * g) =
      (infiniteValueKernel D w).degree f * (infiniteValueKernel D w).degree g :=
  FrobenioidValueKernel.degree_mul _ f g

/-- **Power law of the finite value kernel** (REQ-2 docking theorem of
`PrimeStripFrobenioidCategorySkeleton`): the realified degree of `f^n` is
`n` times the actual finite value of `f`. -/
theorem finiteValueKernel_realification_pow (v : HeightOneSpectrum (𝓞 F))
    (f : Fˣ) (n : ℕ) :
    (finiteValueKernel D v).realification (f ^ n) =
      (n : ℝ) * (D.finiteDelta f v : ℝ) := by
  simpa [finiteValueKernel, finiteValueMap] using
    (LeanFormal.IUT.frobenioidValueKernelOfValueMap_pow_realification
      (finiteValueMap D v) (fun f g => finiteValueMap_mul D v f g)
      (finiteValueMap_one D v) id (fun _ => rfl) f n)

/-- **Power law of the archimedean value kernel**. -/
theorem infiniteValueKernel_realification_pow (w : NumberField.InfinitePlace F)
    (f : Fˣ) (n : ℕ) :
    (infiniteValueKernel D w).realification (f ^ n) =
      (n : ℝ) * D.infiniteDelta f w := by
  simpa [infiniteValueKernel, infiniteValueMap] using
    (LeanFormal.IUT.frobenioidValueKernelOfValueMap_pow_realification
      (infiniteValueMap D w) (fun f g => infiniteValueMap_mul D w f g)
      (infiniteValueMap_one D w) id (fun _ => rfl) f n)

/-- **Power law of the unified value kernel**. -/
theorem placeValueKernel_realification_pow (place : ValuePlace F) (f : Fˣ) (n : ℕ) :
    (placeValueKernel D place).realification (f ^ n) =
      (n : ℝ) * placeValueMap D place f := by
  simpa [placeValueKernel] using
    (LeanFormal.IUT.frobenioidValueKernelOfValueMap_pow_realification
      (placeValueMap D place) (fun f g => placeValueMap_mul D place f g)
      (placeValueMap_one D place) id (fun _ => rfl) f n)

/-- The finite value kernel at the actual number-field place data computes the
backend principal-divisor finite coordinate. -/
theorem numberFieldFiniteValueKernel_realification_eq_principalDivisor
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (finiteValueKernel (numberFieldGlobalPlaceData (F := F)) v).realification f =
      (principalDivisorFinite f v : ℝ) := by
  rw [finiteValueKernel_realification_apply, numberFieldGlobalPlaceData_finiteDelta,
    principalDivisorFinite_apply]

/-- The archimedean value kernel at the actual number-field place data computes
the backend principal-divisor archimedean coordinate. -/
theorem numberFieldInfiniteValueKernel_realification_eq_principalDivisor
    (w : NumberField.InfinitePlace F) (f : Fˣ) :
    (infiniteValueKernel (numberFieldGlobalPlaceData (F := F)) w).realification f =
      principalDivisorInfinite f w := by
  rw [infiniteValueKernel_realification_apply, numberFieldGlobalPlaceData_infiniteDelta,
    principalDivisorInfinite_apply]

/-- The assembled per-place value kernel data of the actual number-field place
data: a reduced Frobenioid value kernel at every finite place and at every
archimedean place, with its realification identified with the actual local
value map. -/
structure PlaceValueKernelData (D : GlobalPlaceData F) where
  /-- The value kernel at each finite place. -/
  finiteKernel : (v : HeightOneSpectrum (𝓞 F)) → FrobenioidValueKernel Fˣ
  /-- The value kernel at each archimedean place. -/
  infiniteKernel : (w : NumberField.InfinitePlace F) → FrobenioidValueKernel Fˣ
  /-- The finite-kernel realifications are the actual finite value maps. -/
  finiteKernel_realification :
    ∀ v, (finiteKernel v).realification = finiteValueMap D v
  /-- The archimedean-kernel realifications are the actual archimedean value
  maps. -/
  infiniteKernel_realification :
    ∀ w, (infiniteKernel w).realification = infiniteValueMap D w

/-- The per-place value-kernel data assembled from the actual value maps. -/
def placeValueKernelData : PlaceValueKernelData D where
  finiteKernel := finiteValueKernel D
  infiniteKernel := infiniteValueKernel D
  finiteKernel_realification := finiteValueKernel_realification D
  infiniteKernel_realification := infiniteValueKernel_realification D

/-- The assembled finite kernels are the finite value kernels. -/
@[simp]
theorem placeValueKernelData_finiteKernel (v : HeightOneSpectrum (𝓞 F)) :
    (placeValueKernelData D).finiteKernel v = finiteValueKernel D v :=
  rfl

/-- The assembled archimedean kernels are the archimedean value kernels. -/
@[simp]
theorem placeValueKernelData_infiniteKernel (w : NumberField.InfinitePlace F) :
    (placeValueKernelData D).infiniteKernel w = infiniteValueKernel D w :=
  rfl

end ValueKernels


/-! ## 3. The K1/K2 link layers of two place data linked by a faithful domain
isomorphism -/

section FaithfulDomainLinks

variable {F' : Type u} [Field F'] [NumberField F']
variable {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}

/-- The identity faithful domain isomorphism of a place data: the identity field
equivalence and the identity place maps preserve the local value coordinates. -/
def FaithfulDomainIsomorphism.identity (D : GlobalPlaceData F) :
    FaithfulDomainIsomorphism D D where
  fieldEquiv := RingEquiv.refl F
  finitePlaceMap := id
  infinitePlaceMap := id
  finiteDelta_preserved := by
    intro f v
    have h : unitsMapOfRingEquiv (RingEquiv.refl F) f = f := by
      ext
      rfl
    rw [h]
    rfl
  infiniteDelta_preserved := by
    intro f w
    have h : unitsMapOfRingEquiv (RingEquiv.refl F) f = f := by
      ext
      rfl
    rw [h]
    rfl

/-- The K1/K2 link layer between the actual finite value maps at the place `v`
of `D` and its image under a genuine faithful domain isomorphism. -/
def faithfulFiniteValueLink (sigma : FaithfulDomainIsomorphism D D')
    (v : HeightOneSpectrum (𝓞 F)) : PrimeStripFrobenioidLinkLayer Fˣ F'ˣ :=
  LeanFormal.IUT.K1K2Realization.primeStripFrobenioidLinkLayerOfValueMaps
    (finiteValueMap D v) (fun f g => finiteValueMap_mul D v f g)
    (finiteValueMap_one D v) id (fun _ => rfl)
    (finiteValueMap D' (sigma.finitePlaceMap v))
    (fun f g => finiteValueMap_mul D' (sigma.finitePlaceMap v) f g)
    (finiteValueMap_one D' (sigma.finitePlaceMap v)) id (fun _ => rfl)
    (unitsMapOfRingEquiv sigma.fieldEquiv)
    (by
      intro f
      have h := sigma.finiteDelta_preserved f v
      change ((D'.finiteDelta (unitsMapOfRingEquiv sigma.fieldEquiv f)
        (sigma.finitePlaceMap v) : ℤ) : ℝ) = ((D.finiteDelta f v : ℤ) : ℝ)
      rw [h])
    (by intro f; rfl)
    (unitsMapOfRingEquiv sigma.fieldEquiv).symm
    (by
      intro g
      have h := sigma.finiteDelta_preserved
        ((unitsMapOfRingEquiv sigma.fieldEquiv).symm g) v
      rw [show unitsMapOfRingEquiv sigma.fieldEquiv
          ((unitsMapOfRingEquiv sigma.fieldEquiv).symm g) = g from
        Equiv.apply_symm_apply _ g] at h
      change ((D.finiteDelta ((unitsMapOfRingEquiv sigma.fieldEquiv).symm g) v : ℤ) : ℝ) =
        ((D'.finiteDelta g (sigma.finitePlaceMap v) : ℤ) : ℝ)
      rw [h])
    (by intro g; rfl)

/-- The K1/K2 link layer between the actual archimedean value maps at the place
`w` of `D` and its image under a genuine faithful domain isomorphism. -/
def faithfulInfiniteValueLink (sigma : FaithfulDomainIsomorphism D D')
    (w : NumberField.InfinitePlace F) : PrimeStripFrobenioidLinkLayer Fˣ F'ˣ :=
  LeanFormal.IUT.K1K2Realization.primeStripFrobenioidLinkLayerOfValueMaps
    (infiniteValueMap D w) (fun f g => infiniteValueMap_mul D w f g)
    (infiniteValueMap_one D w) id (fun _ => rfl)
    (infiniteValueMap D' (sigma.infinitePlaceMap w))
    (fun f g => infiniteValueMap_mul D' (sigma.infinitePlaceMap w) f g)
    (infiniteValueMap_one D' (sigma.infinitePlaceMap w)) id (fun _ => rfl)
    (unitsMapOfRingEquiv sigma.fieldEquiv)
    (by
      intro f
      have h := sigma.infiniteDelta_preserved f w
      change D'.infiniteDelta (unitsMapOfRingEquiv sigma.fieldEquiv f)
        (sigma.infinitePlaceMap w) = D.infiniteDelta f w
      rw [h])
    (by intro f; rfl)
    (unitsMapOfRingEquiv sigma.fieldEquiv).symm
    (by
      intro g
      have h := sigma.infiniteDelta_preserved
        ((unitsMapOfRingEquiv sigma.fieldEquiv).symm g) w
      rw [show unitsMapOfRingEquiv sigma.fieldEquiv
          ((unitsMapOfRingEquiv sigma.fieldEquiv).symm g) = g from
        Equiv.apply_symm_apply _ g] at h
      change D.infiniteDelta ((unitsMapOfRingEquiv sigma.fieldEquiv).symm g) w =
        D'.infiniteDelta g (sigma.infinitePlaceMap w)
      rw [h])
    (by intro g; rfl)

/-- The local value kernel of the finite link is the finite value kernel of the
source place. -/
theorem faithfulFiniteValueLink_localFrobenioid (sigma : FaithfulDomainIsomorphism D D')
    (v : HeightOneSpectrum (𝓞 F)) :
    (faithfulFiniteValueLink sigma v).localFrobenioid = finiteValueKernel D v :=
  rfl

/-- The global value kernel of the finite link is the finite value kernel of the
target place. -/
theorem faithfulFiniteValueLink_globalFrobenioid (sigma : FaithfulDomainIsomorphism D D')
    (v : HeightOneSpectrum (𝓞 F)) :
    (faithfulFiniteValueLink sigma v).globalFrobenioid =
      finiteValueKernel D' (sigma.finitePlaceMap v) :=
  rfl

/-- The `modMap` of the finite link is the unit map induced by the field
equivalence. -/
theorem faithfulFiniteValueLink_modMap (sigma : FaithfulDomainIsomorphism D D')
    (v : HeightOneSpectrum (𝓞 F)) :
    (faithfulFiniteValueLink sigma v).modMap = unitsMapOfRingEquiv sigma.fieldEquiv :=
  rfl

/-- The `MODMap` of the finite link is the inverse unit map. -/
theorem faithfulFiniteValueLink_MODMap (sigma : FaithfulDomainIsomorphism D D')
    (v : HeightOneSpectrum (𝓞 F)) :
    (faithfulFiniteValueLink sigma v).MODMap =
      (unitsMapOfRingEquiv sigma.fieldEquiv).symm :=
  rfl

/-- The local realification of the finite link is the actual finite value of the
source place. -/
theorem faithfulFiniteValueLink_local_realification
    (sigma : FaithfulDomainIsomorphism D D') (v : HeightOneSpectrum (𝓞 F))
    (f : Fˣ) :
    (faithfulFiniteValueLink sigma v).localFrobenioid.realification f =
      (D.finiteDelta f v : ℝ) :=
  rfl

/-- The global realification of the finite link is the actual finite value of the
target place. -/
theorem faithfulFiniteValueLink_global_realification
    (sigma : FaithfulDomainIsomorphism D D') (v : HeightOneSpectrum (𝓞 F))
    (g : F'ˣ) :
    (faithfulFiniteValueLink sigma v).globalFrobenioid.realification g =
      (D'.finiteDelta g (sigma.finitePlaceMap v) : ℝ) :=
  rfl

/-- **localFrobenioid degree readback** for the finite link (the REQ-2 docking
theorem of `PrimeStripFrobenioidCategorySkeleton`), in actual coordinates. -/
theorem faithfulFiniteValueLink_localFrobenioid_degree
    (sigma : FaithfulDomainIsomorphism D D') (v : HeightOneSpectrum (𝓞 F))
    (f : Fˣ) :
    (faithfulFiniteValueLink sigma v).localFrobenioid.degree f =
      Multiplicative.ofAdd ((D.finiteDelta f v : ℝ)) := by
  simpa [faithfulFiniteValueLink, finiteValueMap] using
    (LeanFormal.IUT.primeStripFrobenioidLinkLayerOfValueMaps_localFrobenioid_degree
      (finiteValueMap D v) (fun f g => finiteValueMap_mul D v f g)
      (finiteValueMap_one D v) id (fun _ => rfl)
      (finiteValueMap D' (sigma.finitePlaceMap v))
      (fun f g => finiteValueMap_mul D' (sigma.finitePlaceMap v) f g)
      (finiteValueMap_one D' (sigma.finitePlaceMap v)) id (fun _ => rfl)
      (unitsMapOfRingEquiv sigma.fieldEquiv) _ _
      (unitsMapOfRingEquiv sigma.fieldEquiv).symm _ _ f)

/-- **mod compatibility** for the finite link: the realified value of the image
of `f` under the honest unit transport is the actual finite value of `f`. -/
theorem faithfulFiniteValueLink_mod_realification
    (sigma : FaithfulDomainIsomorphism D D') (v : HeightOneSpectrum (𝓞 F))
    (f : Fˣ) :
    (faithfulFiniteValueLink sigma v).globalFrobenioid.realification
        ((faithfulFiniteValueLink sigma v).modMap f) =
      (D.finiteDelta f v : ℝ) := by
  rw [PrimeStripFrobenioidLinkLayer.mod_realification,
    faithfulFiniteValueLink_local_realification]

/-- **MOD compatibility** for the finite link: the realified value of the image
of `g` under the inverse unit transport is the actual finite value of `g` at
the target place. -/
theorem faithfulFiniteValueLink_MOD_realification
    (sigma : FaithfulDomainIsomorphism D D') (v : HeightOneSpectrum (𝓞 F))
    (g : F'ˣ) :
    (faithfulFiniteValueLink sigma v).localFrobenioid.realification
        ((faithfulFiniteValueLink sigma v).MODMap g) =
      (D'.finiteDelta g (sigma.finitePlaceMap v) : ℝ) := by
  rw [PrimeStripFrobenioidLinkLayer.MOD_realification,
    faithfulFiniteValueLink_global_realification]

/-- The degree-level mod compatibility for the finite link in actual
coordinates. -/
theorem faithfulFiniteValueLink_mod_degree
    (sigma : FaithfulDomainIsomorphism D D') (v : HeightOneSpectrum (𝓞 F))
    (f : Fˣ) :
    (faithfulFiniteValueLink sigma v).globalFrobenioid.degree
        ((faithfulFiniteValueLink sigma v).modMap f) =
      Multiplicative.ofAdd ((D.finiteDelta f v : ℝ)) := by
  rw [(faithfulFiniteValueLink sigma v).mod_degree f]
  exact faithfulFiniteValueLink_localFrobenioid_degree sigma v f

/-- The degree-level MOD compatibility for the finite link in actual
coordinates. -/
theorem faithfulFiniteValueLink_MOD_degree
    (sigma : FaithfulDomainIsomorphism D D') (v : HeightOneSpectrum (𝓞 F))
    (g : F'ˣ) :
    (faithfulFiniteValueLink sigma v).localFrobenioid.degree
        ((faithfulFiniteValueLink sigma v).MODMap g) =
      Multiplicative.ofAdd ((D'.finiteDelta g (sigma.finitePlaceMap v) : ℝ)) := by
  rw [(faithfulFiniteValueLink sigma v).MOD_degree g]
  exact finiteValueKernel_degree_apply D' (sigma.finitePlaceMap v) g

/-- **localFrobenioid degree readback** for the archimedean link. -/
theorem faithfulInfiniteValueLink_localFrobenioid_degree
    (sigma : FaithfulDomainIsomorphism D D') (w : NumberField.InfinitePlace F)
    (f : Fˣ) :
    (faithfulInfiniteValueLink sigma w).localFrobenioid.degree f =
      Multiplicative.ofAdd (D.infiniteDelta f w) := by
  simpa [faithfulInfiniteValueLink, infiniteValueMap] using
    (LeanFormal.IUT.primeStripFrobenioidLinkLayerOfValueMaps_localFrobenioid_degree
      (infiniteValueMap D w) (fun f g => infiniteValueMap_mul D w f g)
      (infiniteValueMap_one D w) id (fun _ => rfl)
      (infiniteValueMap D' (sigma.infinitePlaceMap w))
      (fun f g => infiniteValueMap_mul D' (sigma.infinitePlaceMap w) f g)
      (infiniteValueMap_one D' (sigma.infinitePlaceMap w)) id (fun _ => rfl)
      (unitsMapOfRingEquiv sigma.fieldEquiv) _ _
      (unitsMapOfRingEquiv sigma.fieldEquiv).symm _ _ f)

/-- **mod compatibility** for the archimedean link in actual coordinates. -/
theorem faithfulInfiniteValueLink_mod_realification
    (sigma : FaithfulDomainIsomorphism D D') (w : NumberField.InfinitePlace F)
    (f : Fˣ) :
    (faithfulInfiniteValueLink sigma w).globalFrobenioid.realification
        ((faithfulInfiniteValueLink sigma w).modMap f) =
      D.infiniteDelta f w := by
  rw [PrimeStripFrobenioidLinkLayer.mod_realification]
  rfl

/-- **MOD compatibility** for the archimedean link in actual coordinates. -/
theorem faithfulInfiniteValueLink_MOD_realification
    (sigma : FaithfulDomainIsomorphism D D') (w : NumberField.InfinitePlace F)
    (g : F'ˣ) :
    (faithfulInfiniteValueLink sigma w).localFrobenioid.realification
        ((faithfulInfiniteValueLink sigma w).MODMap g) =
      D'.infiniteDelta g (sigma.infinitePlaceMap w) := by
  rw [PrimeStripFrobenioidLinkLayer.MOD_realification]
  rfl

/-- The identity-place comparison finite link: the special case of a faithful
domain isomorphism with identity field equivalence and identity place maps. -/
def identityFiniteValueLink (D : GlobalPlaceData F) (v : HeightOneSpectrum (𝓞 F)) :
    PrimeStripFrobenioidLinkLayer Fˣ Fˣ :=
  faithfulFiniteValueLink (FaithfulDomainIsomorphism.identity D) v

/-- The identity-place comparison archimedean link. -/
def identityInfiniteValueLink (D : GlobalPlaceData F)
    (w : NumberField.InfinitePlace F) : PrimeStripFrobenioidLinkLayer Fˣ Fˣ :=
  faithfulInfiniteValueLink (FaithfulDomainIsomorphism.identity D) w

/-- The actual-coordinate mod readback at the identity-place comparison. -/
theorem identityFiniteValueLink_mod_realification (D : GlobalPlaceData F)
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (identityFiniteValueLink D v).globalFrobenioid.realification
        ((identityFiniteValueLink D v).modMap f) = (D.finiteDelta f v : ℝ) :=
  faithfulFiniteValueLink_mod_realification (FaithfulDomainIsomorphism.identity D) v f

/-- The actual-coordinate local degree readback at the identity-place
comparison. -/
theorem identityFiniteValueLink_localFrobenioid_degree (D : GlobalPlaceData F)
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (identityFiniteValueLink D v).localFrobenioid.degree f =
      Multiplicative.ofAdd ((D.finiteDelta f v : ℝ)) :=
  faithfulFiniteValueLink_localFrobenioid_degree
    (FaithfulDomainIsomorphism.identity D) v f

end FaithfulDomainLinks

/-! ## 4. Range/image hypotheses and their exact consequences

The identifications `v((Qp)^x) = Q` and the degree image `Q * log p` are range
statements on the value map.  The K1/K2 value-kernel and link-layer laws do not
constrain the range (`zeroValueMapKernel_not_rationalImage`), so they are exposed
here as named hypotheses; only their exact consequences are proved. -/

section RangeHypotheses

variable (D : GlobalPlaceData F)

/-- Named hypothesis: the finite value map at `v` has rational image (the
downstream identification `v((Qp)^x) = Q` at the finite place). -/
def FiniteValueMapRationalImage (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  LeanFormal.IUT.K1K2Realization.ValueMapRationalImage (finiteValueMap D v)

/-- Named hypothesis: the archimedean value map at `w` has rational image. -/
def InfiniteValueMapRationalImage (w : NumberField.InfinitePlace F) : Prop :=
  LeanFormal.IUT.K1K2Realization.ValueMapRationalImage (infiniteValueMap D w)

/-- Named hypothesis: the unified value map at a place has rational image. -/
def PlaceValueMapRationalImage (place : ValuePlace F) : Prop :=
  LeanFormal.IUT.K1K2Realization.ValueMapRationalImage (placeValueMap D place)

/-- The scaled rational image (the degree image `Q * log p`) follows from the
rational-image hypothesis; this is the only implication supplied by the K1/K2
entry. -/
theorem finiteValueMap_scaledRationalImage_of_hypothesis
    (v : HeightOneSpectrum (𝓞 F)) (scale : ℝ)
    (h : FiniteValueMapRationalImage D v) :
    LeanFormal.IUT.K1K2Realization.ValueMapScaledRationalImage scale
      (finiteValueMap D v) :=
  LeanFormal.IUT.K1K2Realization.valueMapScaledRationalImage_of_rationalImage h

/-- The scaled rational image at a place follows from the rational-image
hypothesis. -/
theorem placeValueMap_scaledRationalImage_of_hypothesis
    (place : ValuePlace F) (scale : ℝ) (h : PlaceValueMapRationalImage D place) :
    LeanFormal.IUT.K1K2Realization.ValueMapScaledRationalImage scale
      (placeValueMap D place) :=
  LeanFormal.IUT.K1K2Realization.valueMapScaledRationalImage_of_rationalImage h

/-- **Degree image under the rational-image hypothesis**: the range of the
scaled realified value is the lattice `Q * scale`. -/
theorem finiteValueKernel_scaled_degree_range_of_hypothesis
    (v : HeightOneSpectrum (𝓞 F)) (scale : ℝ)
    (h : FiniteValueMapRationalImage D v) :
    Set.range (fun f : Fˣ =>
        Multiplicative.ofAdd (scale * (D.finiteDelta f v : ℝ))) =
      Set.range (fun q : ℚ => Multiplicative.ofAdd (scale * (q : ℝ))) := by
  have h' := LeanFormal.IUT.K1K2Realization.valueMapScaledRationalImage_of_rationalImage
    (scale := scale) h
  ext m
  constructor
  · rintro ⟨f, rfl⟩
    have hy : scale * finiteValueMap D v f ∈
        Set.range (fun q : ℚ => scale * (q : ℝ)) := by
      rw [← h']
      exact ⟨f, rfl⟩
    obtain ⟨q, hq⟩ := hy
    exact ⟨q, congrArg Multiplicative.ofAdd hq⟩
  · rintro ⟨q, rfl⟩
    change ∃ f : Fˣ, Multiplicative.ofAdd (scale * (D.finiteDelta f v : ℝ)) =
      Multiplicative.ofAdd (scale * (q : ℝ))
    have hq : scale * (q : ℝ) ∈
        Set.range (fun x : Fˣ => scale * finiteValueMap D v x) := by
      rw [h']
      exact ⟨q, rfl⟩
    obtain ⟨f, hf⟩ := hq
    have hf' : scale * (D.finiteDelta f v : ℝ) = scale * (q : ℝ) := hf
    exact ⟨f, congrArg Multiplicative.ofAdd hf'⟩

/-- **Degree range under the rational-image hypothesis**: the range of the
finite value-kernel degree is `Multiplicative.ofAdd` of the rationals. -/
theorem finiteValueKernel_degree_range_of_hypothesis
    (v : HeightOneSpectrum (𝓞 F)) (h : FiniteValueMapRationalImage D v) :
    Set.range (fun f : Fˣ => (finiteValueKernel D v).degree f) =
      Set.range (fun q : ℚ => Multiplicative.ofAdd ((q : ℝ))) := by
  have h' : Set.range (finiteValueMap D v) =
      Set.range (fun q : ℚ => (q : ℝ)) := h
  ext m
  constructor
  · rintro ⟨f, rfl⟩
    change (finiteValueKernel D v).degree f ∈
      Set.range (fun q : ℚ => Multiplicative.ofAdd ((q : ℝ)))
    rw [finiteValueKernel_degree_apply]
    have hy : finiteValueMap D v f ∈ Set.range (fun q : ℚ => (q : ℝ)) := by
      rw [← h']
      exact ⟨f, rfl⟩
    obtain ⟨q, hq⟩ := hy
    exact ⟨q, congrArg Multiplicative.ofAdd hq⟩
  · rintro ⟨q, rfl⟩
    change ∃ f : Fˣ, (finiteValueKernel D v).degree f =
      Multiplicative.ofAdd ((q : ℝ))
    have hq : (q : ℝ) ∈ Set.range (finiteValueMap D v) := by
      rw [h']
      exact ⟨q, rfl⟩
    obtain ⟨f, hf⟩ := hq
    have hf' : (D.finiteDelta f v : ℝ) = (q : ℝ) := hf
    exact ⟨f, by rw [finiteValueKernel_degree_apply, hf']⟩

/-- **The card witness**: a K1/K2 value kernel whose realification is the
constant zero map is admissible, but its image is not the rational line.  Hence
the range hypotheses above are genuinely additional inputs, not consequences of
the value-kernel laws. -/
theorem zeroValueMapKernel_not_rationalImage :
    ¬ LeanFormal.IUT.K1K2Realization.ValueMapRationalImage
        ((LeanFormal.IUT.K1K2Realization.zeroValueMapKernel (Fˣ)).realification) :=
  LeanFormal.IUT.K1K2Realization.zeroValueMapKernel_not_rationalImage (Fˣ)

/-- The degree-image form of the downstream `Q * log p` identification, stated
as a named hypothesis and unfolded through the K1/K2 scaled image. -/
def FiniteDegreeImageHypothesis (v : HeightOneSpectrum (𝓞 F)) (scale : ℝ) : Prop :=
  LeanFormal.IUT.K1K2Realization.ValueMapScaledRationalImage scale
    (finiteValueMap D v)

/-- The scaled rational-image hypothesis implies the degree-image hypothesis. -/
theorem finiteDegreeImageHypothesis_of_rationalImage
    (v : HeightOneSpectrum (𝓞 F)) (scale : ℝ)
    (h : FiniteValueMapRationalImage D v) :
    FiniteDegreeImageHypothesis D v scale :=
  LeanFormal.IUT.K1K2Realization.valueMapScaledRationalImage_of_rationalImage h

end RangeHypotheses

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
