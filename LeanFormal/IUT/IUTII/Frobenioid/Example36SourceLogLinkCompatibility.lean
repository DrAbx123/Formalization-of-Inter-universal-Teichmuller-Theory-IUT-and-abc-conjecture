/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanFormal.IUT.IUTII.Frobenioid.Example36ValueMapTransportCorrection
import LeanFormal.IUT.IUTII.Frobenioid.Example36QuadraticTransportStrict
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceLogKummerIdentification
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmFunctoriality
import LeanFormal.IUT.Foundations.LocalFields.LogarithmSeriesTransport
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionNormFormulaActual
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension
import Mathlib.Tactic

/-!
# Source log-link / transport compatibility squares

This file constructs the actual local-field log-link/transport compatibility
squares needed for the source side of the Example 3.6 / IUT II Frobenioid
layer.  There are no frozen identification cards and no `rfl`-only comparison
to a concrete model.

## What is constructed

* `integralRingMapOfMapsIntegers` and `integralUnitMapOfMapsIntegers`: the
  actual maps of valuation rings and their unit groups induced by a ring map
  that preserves the valuation-integer subrings.
* `unitLog_map_of_continuous`: the square
  `e (unitLog u) = unitLog (integralUnitMap u)` for every integral unit `u`,
  for a continuous ring map `e` that preserves integral units and principal
  units.  Continuity, rather than isometry, is the hypothesis: this is the
  form needed for completion maps with nontrivial ramification.
* `map_mem_integralLogShell_of_continuous`: the induced transport of the
  actual scaled log-shell `(logShellScale p)⁻¹ • log(Oˣ)`.
* `scaled_unitLog_map_of_continuous` and `integralLogShellTransport`: the
  same square on the scaled log-link and the induced additive map of actual
  log-shells.
* `sourceTheaterScalarMap`: the actual scalar transport of the source
  theater, namely the composite of the actual rational completion at the
  concrete place with the actual finite-place completion embedding.  It is
  proved equal to `padicCompletionHom` and to the composite through
  `completionMap`.
* `sourceTheater_unitLog_square`, `sourceTheater_scaledLog_square`,
  `sourceTheater_logShell_transport`: the concrete compatibility squares for
  that actual transport, together with the value/norm compatibility
  `sourceTheaterScalarMap_norm` and injectivity of the transport.

## What is not constructed

The independent source log-Kummer carrier of
`Example36SourceLogKummerIdentification` lives on `ℚ_[l]` (the source local
field of the Tate local carrier, with `q = l`), while the source theater's
concrete log-shell lives on the Gaussian completion
`NormalizedCompletion concretePlace`.  The tree does not construct an actual
continuous ring map `ℚ_[l] →+* concreteLogShellField` (or an identification of
the two log-Kummer carriers) induced by the source data; this is the exact
missing source link.  Consequently the paper's full horizontal log-link /
Θ-link between distinct theaters is not constructed here.  The maximal actual
square along the transport that the source place data does determine, the
base rational local field `PadicScalarField concretePlace →+* K_v`, is proved
below.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open IsDedekindDomain NumberField
open scoped NumberField
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm

universe u

section GeneralLogShellFunctoriality

variable {K L : Type*} [NormedField K] [IsUltrametricDist K]
variable [NormedField L] [IsUltrametricDist L]
variable [CharZero K] [CompleteSpace K] [ProperSpace K]
variable [CharZero L] [CompleteSpace L] [ProperSpace L]
variable {p : ℕ} [Fact p.Prime]
variable [NormedAlgebra ℚ_[p] K] [NormedAlgebra ℚ_[p] L]

/-- A ring map that carries the valuation-integer subring of the source into
the valuation-integer subring of the target. -/
def integralRingMapOfMapsIntegers (e : K →+* L)
    (hInt : ∀ x : K, x ∈ Integers K → e x ∈ Integers L) :
    Integers K →+* Integers L where
  toFun x := ⟨e (x : K), hInt (x : K) x.property⟩
  map_zero' := Subtype.ext e.map_zero
  map_one' := Subtype.ext e.map_one
  map_add' x y := Subtype.ext (e.map_add (x : K) (y : K))
  map_mul' x y := Subtype.ext (e.map_mul (x : K) (y : K))

@[simp]
theorem integralRingMapOfMapsIntegers_apply_coe (e : K →+* L)
    (hInt : ∀ x : K, x ∈ Integers K → e x ∈ Integers L) (x : Integers K) :
    ((integralRingMapOfMapsIntegers e hInt x : Integers L) : L) = e (x : K) :=
  rfl

/-- The induced map on full valuation-integer unit groups. -/
def integralUnitMapOfMapsIntegers (e : K →+* L)
    (hInt : ∀ x : K, x ∈ Integers K → e x ∈ Integers L) :
    (Integers K)ˣ →* (Integers L)ˣ :=
  Units.map (integralRingMapOfMapsIntegers e hInt).toMonoidHom

@[simp]
theorem integralUnitMapOfMapsIntegers_val (e : K →+* L)
    (hInt : ∀ x : K, x ∈ Integers K → e x ∈ Integers L) (u : (Integers K)ˣ) :
    ((integralUnitMapOfMapsIntegers e hInt u).val : L) = e (u.val : K) :=
  rfl

include p

/-- The full logarithm commutes with a continuous ring map that preserves
integral units and principal units.  The exponent used to define the logarithm
may differ in the source and target fields; the proof uses the source exponent
on both sides and the target logarithm's independence of the exponent. -/
theorem unitLog_map_of_continuous (e : K →+* L) (he : Continuous e)
    (hInt : ∀ x : K, x ∈ Integers K → e x ∈ Integers L)
    (hPrincipal : ∀ u : (Integers K)ˣ, u ∈ principalUnits →
      integralUnitMapOfMapsIntegers e hInt u ∈ principalUnits)
    (u : (Integers K)ˣ) :
    e (unitLog u) = unitLog (integralUnitMapOfMapsIntegers e hInt u) := by
  let n := integralUnitExponent (K := K)
  have hn : n ≠ 0 := ne_of_gt integralUnitExponent_pos
  have hu : u ^ n ∈ principalUnits := pow_integralUnitExponent_mem u
  have hpow : (integralUnitMapOfMapsIntegers e hInt u) ^ n =
      integralUnitMapOfMapsIntegers e hInt (u ^ n) :=
    (map_pow (integralUnitMapOfMapsIntegers e hInt) u n).symm
  have hv : (integralUnitMapOfMapsIntegers e hInt u) ^ n ∈ principalUnits := by
    rw [hpow]
    exact hPrincipal _ hu
  have hoffset : (((integralUnitMapOfMapsIntegers e hInt u) ^ n).val : L) - 1 =
      e (((u ^ n).val : K) - 1) := by
    rw [hpow, integralUnitMapOfMapsIntegers_val, map_sub, map_one]
  rw [unitLog_eq_withExponent (K := K) (p := p) (n := n) u hn hu,
    unitLog_eq_withExponent (K := L) (p := p) (n := n)
      (integralUnitMapOfMapsIntegers e hInt u) hn hv]
  dsimp only [unitLogWithExponent]
  rw [map_div₀, map_natCast, hoffset,
    @log1p_map_of_continuous K _ _ _ p _ _ L _ e he _ ((mem_principalUnits_iff _).mp hu)]

/-- The actual scaled logarithmic image is transported by a continuous ring map
that preserves integral units and principal units.  This is the non-isometric
form needed for completion maps with nontrivial ramification. -/
theorem map_mem_integralLogShell_of_continuous (e : K →+* L) (he : Continuous e)
    (hInt : ∀ x : K, x ∈ Integers K → e x ∈ Integers L)
    (hPrincipal : ∀ u : (Integers K)ˣ, u ∈ principalUnits →
      integralUnitMapOfMapsIntegers e hInt u ∈ principalUnits)
    {x : K} (hx : x ∈ integralLogShell (K := K) (p := p)) :
    e x ∈ integralLogShell (K := L) (p := p) := by
  obtain ⟨u, rfl⟩ := hx
  refine ⟨integralUnitMapOfMapsIntegers e hInt u, ?_⟩
  change (logShellScale p : L)⁻¹ *
      unitLog (integralUnitMapOfMapsIntegers e hInt u) =
    e ((logShellScale p : K)⁻¹ * unitLog u)
  rw [← unitLog_map_of_continuous (p := p) e he hInt hPrincipal u, map_mul,
    map_inv₀, map_natCast]

end GeneralLogShellFunctoriality

/-! ## 2. The scaled log-link square on the actual log-shells -/

section ScaledLogLinkSquare

variable {K L : Type*} [NormedField K] [IsUltrametricDist K]
variable [NormedField L] [IsUltrametricDist L]
variable [CharZero K] [CompleteSpace K] [ProperSpace K]
variable [CharZero L] [CompleteSpace L] [ProperSpace L]
variable {p : ℕ} [Fact p.Prime]
variable [NormedAlgebra ℚ_[p] K] [NormedAlgebra ℚ_[p] L]

/-- The scaled log-link square: transporting the scaled logarithm of an
integral unit along a continuous integral-unit-preserving map is the scaled
logarithm of the transported unit. -/
theorem scaled_unitLog_map_of_continuous (e : K →+* L) (he : Continuous e)
    (hInt : ∀ x : K, x ∈ Integers K → e x ∈ Integers L)
    (hPrincipal : ∀ u : (Integers K)ˣ, u ∈ principalUnits →
      integralUnitMapOfMapsIntegers e hInt u ∈ principalUnits)
    (u : (Integers K)ˣ) :
    e ((logShellScale p : K)⁻¹ * unitLog u) =
      (logShellScale p : L)⁻¹ *
        unitLog (integralUnitMapOfMapsIntegers e hInt u) := by
  rw [map_mul, map_inv₀, map_natCast,
    unitLog_map_of_continuous (p := p) e he hInt hPrincipal u]

/-- The actual transport restricted to the scaled log-shells. -/
noncomputable def integralLogShellTransport (e : K →+* L) (he : Continuous e)
    (hInt : ∀ x : K, x ∈ Integers K → e x ∈ Integers L)
    (hPrincipal : ∀ u : (Integers K)ˣ, u ∈ principalUnits →
      integralUnitMapOfMapsIntegers e hInt u ∈ principalUnits) :
    integralLogShell (K := K) (p := p) →+ integralLogShell (K := L) (p := p) where
  toFun x :=
    ⟨e (x : K),
      map_mem_integralLogShell_of_continuous (p := p) e he hInt hPrincipal x.property⟩
  map_zero' := Subtype.ext (map_zero e)
  map_add' x y := Subtype.ext (map_add e (x : K) (y : K))

@[simp]
theorem integralLogShellTransport_apply_coe (e : K →+* L) (he : Continuous e)
    (hInt : ∀ x : K, x ∈ Integers K → e x ∈ Integers L)
    (hPrincipal : ∀ u : (Integers K)ˣ, u ∈ principalUnits →
      integralUnitMapOfMapsIntegers e hInt u ∈ principalUnits)
    (x : integralLogShell (K := K) (p := p)) :
    ((integralLogShellTransport e he hInt hPrincipal x :
        integralLogShell (K := L) (p := p)) : L) = e (x : K) :=
  rfl

/-- On the canonical scaled generators of the log-shell, the induced
log-shell transport is exactly the scaled log-link square. -/
theorem integralLogShellTransport_scaled_unitLog (e : K →+* L) (he : Continuous e)
    (hInt : ∀ x : K, x ∈ Integers K → e x ∈ Integers L)
    (hPrincipal : ∀ u : (Integers K)ˣ, u ∈ principalUnits →
      integralUnitMapOfMapsIntegers e hInt u ∈ principalUnits)
    (u : (Integers K)ˣ) :
    integralLogShellTransport e he hInt hPrincipal
        ⟨(logShellScale p : K)⁻¹ * unitLog u, ⟨u, rfl⟩⟩ =
      ⟨(logShellScale p : L)⁻¹ *
          unitLog (integralUnitMapOfMapsIntegers e hInt u),
        ⟨integralUnitMapOfMapsIntegers e hInt u, rfl⟩⟩ :=
  Subtype.ext (scaled_unitLog_map_of_continuous e he hInt hPrincipal u)

end ScaledLogLinkSquare

/-! ## 3. The actual source-theater transport

The source theater's concrete place is a finite place of the Gaussian field
over the rational prime five.  The actual transport determined by that place
data is the composite of the rational completion below the place with the
finite-place completion embedding; it is the map
`PadicScalarField concretePlace →+* concreteLogShellField`.  The squares
below are stated for this actual map, not for a supplied comparison datum. -/

section SourceTheaterTransport

local instance sourceLogLinkGaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice

/-- The actual rational local field below the source theater's concrete place. -/
abbrev sourceBaseLocalField : Type := PadicScalarField concretePlace

/-- The actual local field of the source theater: the normalized completion of
the Gaussian field at the concrete place. -/
abbrev sourceTheaterLocalField : Type := concreteLogShellField

/-- The actual scalar transport determined by the source theater's concrete
place data. -/
noncomputable def sourceTheaterScalarMap :
    sourceBaseLocalField →+* sourceTheaterLocalField :=
  algebraMap sourceBaseLocalField sourceTheaterLocalField

/-- The scalar transport is the actual `padicCompletionHom` of the concrete
place, not an auxiliary comparison map. -/
theorem sourceTheaterScalarMap_eq_padicCompletionHom :
    sourceTheaterScalarMap = padicCompletionHom concretePlace :=
  padicCompletionAlgebra_algebraMap concretePlace

/-- The actual scalar transport is continuous. -/
theorem sourceTheaterScalarMap_continuous : Continuous sourceTheaterScalarMap :=
  continuous_algebraMap _ _

/-- The actual value map (normalized norm) commutes with the source-theater
transport. -/
theorem sourceTheaterScalarMap_norm (x : sourceBaseLocalField) :
    ‖sourceTheaterScalarMap x‖ = ‖x‖ := by
  change ‖(algebraMap (PadicScalarField concretePlace)
    (NormalizedCompletion concretePlace)) x‖ = ‖x‖
  exact normalizedCompletion_norm_algebraMap concretePlace x

/-- The source-theater transport carries valuation integers to valuation
integers. -/
theorem sourceTheaterScalarMap_mem_integers {x : sourceBaseLocalField}
    (hx : x ∈ Integers sourceBaseLocalField) :
    sourceTheaterScalarMap x ∈ Integers sourceTheaterLocalField := by
  rw [mem_integers_iff] at hx ⊢
  rwa [sourceTheaterScalarMap_norm]

/-- The source-theater transport carries principal units to principal units. -/
theorem sourceTheaterScalarMap_mem_principalUnits
    (u : (Integers sourceBaseLocalField)ˣ) (hu : u ∈ principalUnits) :
    integralUnitMapOfMapsIntegers sourceTheaterScalarMap
        (fun _ hx => sourceTheaterScalarMap_mem_integers hx) u ∈ principalUnits := by
  rw [mem_principalUnits_iff] at hu ⊢
  rw [integralUnitMapOfMapsIntegers_val]
  rw [← map_one sourceTheaterScalarMap, ← map_sub, sourceTheaterScalarMap_norm]
  exact hu

/-- The actual source-theater log-link square: the full logarithm commutes
with the actual place-completion transport. -/
theorem sourceTheater_unitLog_square (u : (Integers sourceBaseLocalField)ˣ) :
    sourceTheaterScalarMap (unitLog u) =
      unitLog (integralUnitMapOfMapsIntegers sourceTheaterScalarMap
        (fun _ hx => sourceTheaterScalarMap_mem_integers hx) u) :=
  unitLog_map_of_continuous (p := concreteRationalPrime) sourceTheaterScalarMap
    sourceTheaterScalarMap_continuous
    (fun _ hx => sourceTheaterScalarMap_mem_integers hx)
    sourceTheaterScalarMap_mem_principalUnits u

/-- The actual source-theater scaled log-link square: the paper's scaled
logarithm `(logShellScale p)⁻¹ log` commutes with the transport. -/
theorem sourceTheater_scaledLog_square (u : (Integers sourceBaseLocalField)ˣ) :
    sourceTheaterScalarMap
        ((logShellScale concreteRationalPrime : sourceBaseLocalField)⁻¹ * unitLog u) =
      (logShellScale concreteRationalPrime : sourceTheaterLocalField)⁻¹ *
        unitLog (integralUnitMapOfMapsIntegers sourceTheaterScalarMap
          (fun _ hx => sourceTheaterScalarMap_mem_integers hx) u) :=
  scaled_unitLog_map_of_continuous (p := concreteRationalPrime) sourceTheaterScalarMap
    sourceTheaterScalarMap_continuous
    (fun _ hx => sourceTheaterScalarMap_mem_integers hx)
    sourceTheaterScalarMap_mem_principalUnits u

/-- The actual source-theater log-shell transport: the image of the base
scaled log-shell lies in the source theater's scaled log-shell. -/
theorem sourceTheater_logShell_transport {x : sourceBaseLocalField}
    (hx : x ∈ integralLogShell (K := sourceBaseLocalField) (p := concreteRationalPrime)) :
    sourceTheaterScalarMap x ∈
      integralLogShell (K := sourceTheaterLocalField) (p := concreteRationalPrime) :=
  map_mem_integralLogShell_of_continuous (p := concreteRationalPrime)
    sourceTheaterScalarMap sourceTheaterScalarMap_continuous
    (fun _ hx => sourceTheaterScalarMap_mem_integers hx)
    sourceTheaterScalarMap_mem_principalUnits hx

/-- The induced additive map of actual scaled log-shells. -/
noncomputable def sourceTheaterLogShellMap :
    integralLogShell (K := sourceBaseLocalField) (p := concreteRationalPrime) →+
      integralLogShell (K := sourceTheaterLocalField) (p := concreteRationalPrime) :=
  integralLogShellTransport (p := concreteRationalPrime) sourceTheaterScalarMap
    sourceTheaterScalarMap_continuous
    (fun _ hx => sourceTheaterScalarMap_mem_integers hx)
    sourceTheaterScalarMap_mem_principalUnits

/-- The induced log-shell map sends each canonical scaled log generator to the
scaled log of the transported unit. -/
theorem sourceTheaterLogShellMap_scaledLog (u : (Integers sourceBaseLocalField)ˣ) :
    sourceTheaterLogShellMap
        ⟨(logShellScale concreteRationalPrime : sourceBaseLocalField)⁻¹ * unitLog u,
          ⟨u, rfl⟩⟩ =
      ⟨(logShellScale concreteRationalPrime : sourceTheaterLocalField)⁻¹ *
          unitLog (integralUnitMapOfMapsIntegers sourceTheaterScalarMap
            (fun _ hx => sourceTheaterScalarMap_mem_integers hx) u),
        ⟨integralUnitMapOfMapsIntegers sourceTheaterScalarMap
            (fun _ hx => sourceTheaterScalarMap_mem_integers hx) u, rfl⟩⟩ :=
  integralLogShellTransport_scaled_unitLog (p := concreteRationalPrime)
    sourceTheaterScalarMap sourceTheaterScalarMap_continuous
    (fun _ hx => sourceTheaterScalarMap_mem_integers hx)
    sourceTheaterScalarMap_mem_principalUnits u

/-- The actual source-theater transport is injective. -/
theorem sourceTheaterScalarMap_injective : Function.Injective sourceTheaterScalarMap := by
  intro x y hxy
  have hzero : sourceTheaterScalarMap (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hnorm : ‖x - y‖ = 0 := by
    rw [← sourceTheaterScalarMap_norm, hzero, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-! ## 4. Compatibility with the actual place-localization transport -/

/-- The actual place-localization transport from the rational field to the
Gaussian field at the source theater's concrete place. -/
noncomputable def concreteGaussianPlaceTransport :
    PlaceLocalizationTransport (numberFieldGlobalPlaceData (F := ℚ))
      (numberFieldGlobalPlaceData (F := GaussianField)) :=
  PlaceLocalizationTransport.ofNumberFieldExtension (F := ℚ) (F' := GaussianField)

/-- At the source theater's concrete place, the actual ramification index of
the place-localization transport is one. -/
theorem concreteGaussianPlaceTransport_ramificationIndex :
    concreteGaussianPlaceTransport.ramificationIndex concreteHeightOneSpectrum = 1 := by
  change ramificationIndexAtUpperPlace (F := ℚ) (F' := GaussianField) concreteHeightOneSpectrum = 1
  unfold ramificationIndexAtUpperPlace
  rw [NumberField.FinitePlace.maximalIdeal_mk]
  have hmk : NumberField.FinitePlace.mk concreteHeightOneSpectrum = concreteGaussianFivePlace := by
    rw [concreteHeightOneSpectrum, NumberField.FinitePlace.mk_maximalIdeal]
  rw [hmk]
  exact concreteGaussianFivePlace_relativeRamificationIndex_eq_one

/-- The actual value-transport square along the place-localization transport at
the source theater's concrete place.  The transported value is the value of the
completion image, and the scalar is the actual ramification index. -/
theorem concreteGaussianPlaceTransport_finiteValue_square (f : ℚˣ) :
    finiteValueMap (numberFieldGlobalPlaceData (F := GaussianField)) concreteHeightOneSpectrum
        (unitsMapOfRingHom (algebraMap ℚ GaussianField) f) =
      (concreteGaussianPlaceTransport.ramificationIndex concreteHeightOneSpectrum : ℝ) *
        finiteValueMap (numberFieldGlobalPlaceData (F := ℚ))
          (concreteGaussianPlaceTransport.finitePlaceRestriction concreteHeightOneSpectrum) f :=
  transportedFiniteValueMap_eq concreteGaussianPlaceTransport f concreteHeightOneSpectrum

/-- At the concrete place the actual value transport is value-preserving,
because the actual ramification index is one. -/
theorem concreteGaussianPlaceTransport_finiteValue_eq (f : ℚˣ) :
    finiteValueMap (numberFieldGlobalPlaceData (F := GaussianField)) concreteHeightOneSpectrum
        (unitsMapOfRingHom (algebraMap ℚ GaussianField) f) =
      finiteValueMap (numberFieldGlobalPlaceData (F := ℚ))
        (concreteGaussianPlaceTransport.finitePlaceRestriction concreteHeightOneSpectrum) f := by
  rw [concreteGaussianPlaceTransport_finiteValue_square,
    concreteGaussianPlaceTransport_ramificationIndex]
  norm_num

end SourceTheaterTransport

/-! ## 5. The independent source log-link square at the prime five -/

section SourceLogLinkSquare

/-- The actual source prime label five. -/
def sourceLogLinkFivePrime : PrimeGeFive where
  value := 5
  prime := Nat.prime_five
  ge_five := by norm_num

local instance sourceLogLinkFivePrimeFact : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

@[simp] theorem sourceLogLinkFivePrime_value : sourceLogLinkFivePrime.value = 5 :=
  rfl

/-- The actual source log-link square: Frobenius on principal units commutes
with the p-fold scaling of the source log-shell. -/
theorem sourceLogLink_square (u : sourcePrincipalUnits sourceLogLinkFivePrime) :
    sourceLogKummerShell sourceLogLinkFivePrime
        (sourceFrobenius sourceLogLinkFivePrime u) =
      sourcePScaling sourceLogLinkFivePrime
        (sourceLogKummerShell sourceLogLinkFivePrime u) :=
  sourceLogKummer_square sourceLogLinkFivePrime u

/-- The actual source log-link is nontrivial: the p-fold scaling moves a point
of the source log-shell. -/
theorem sourceLogLink_nontrivial :
    ∃ x : sourceLogShell sourceLogLinkFivePrime,
      sourcePScaling sourceLogLinkFivePrime x ≠ x :=
  sourcePScaling_nontrivial sourceLogLinkFivePrime

end SourceLogLinkSquare

/-! ## 6. The actual ramified value-transport square at Q(sqrt 2) / Q -/

section QuadraticValueTransport

/-- The actual value-transport square at the exact place above (2):
rho_w(phi f) = e_w * rho_v(f), with the genuine ramification index. -/
theorem quadraticTransport_finiteValue_square (f : ℚˣ) :
    finiteValueMap (numberFieldGlobalPlaceData (F := quadraticExampleField))
        sqrtTwoUpperPlace
        (unitsMapOfRingHom (algebraMap ℚ quadraticExampleField) f) =
      (quadraticSquareRootTwoTransport.ramificationIndex sqrtTwoUpperPlace : ℝ) *
        finiteValueMap (numberFieldGlobalPlaceData (F := ℚ)) sqrtTwoRationalPlace f := by
  have h := transportedFiniteValueMap_eq quadraticSquareRootTwoTransport f sqrtTwoUpperPlace
  simpa [sqrtTwoRationalPlace] using h

/-- The transported value of the global unit two at the exact place is two. -/
theorem quadraticTransport_two_finiteValue :
    finiteValueMap (numberFieldGlobalPlaceData (F := quadraticExampleField))
        sqrtTwoUpperPlace
        (unitsMapOfRingHom (algebraMap ℚ quadraticExampleField) quadraticExampleTwoUnit) = 2 := by
  rw [finiteValueMap_apply, quadraticStrict_two_finiteDelta]
  norm_num

/-- The source value of the global unit two at the restricted place is one. -/
theorem quadraticTransport_two_source_finiteValue :
    finiteValueMap (numberFieldGlobalPlaceData (F := ℚ)) sqrtTwoRationalPlace
        quadraticExampleTwoUnit = 1 := by
  rw [finiteValueMap_apply, numberFieldGlobalPlaceData_finiteDelta,
    sqrtTwoRationalPlace_two_value]
  norm_num

/-- Nontriviality of the actual value transport: the source value is one, the
transported value is two, and the actual ramification index is two.  Thus the
transport is not the identity on values. -/
theorem quadraticTransport_nontrivial :
    finiteValueMap (numberFieldGlobalPlaceData (F := quadraticExampleField))
        sqrtTwoUpperPlace
          (unitsMapOfRingHom (algebraMap ℚ quadraticExampleField)
            quadraticExampleTwoUnit) = 2 ∧
      finiteValueMap (numberFieldGlobalPlaceData (F := ℚ)) sqrtTwoRationalPlace
          quadraticExampleTwoUnit = 1 ∧
        quadraticSquareRootTwoTransport.ramificationIndex sqrtTwoUpperPlace = 2 :=
  ⟨quadraticTransport_two_finiteValue, quadraticTransport_two_source_finiteValue,
    quadraticStrict_ramificationIndex⟩

/-- The actual K1/K2 value-kernel square along the same ramified transport. -/
theorem quadraticTransport_valueKernel_square (f : ℚˣ) :
    (finiteValueKernel (numberFieldGlobalPlaceData (F := quadraticExampleField))
        sqrtTwoUpperPlace).realification
        (unitsMapOfRingHom (algebraMap ℚ quadraticExampleField) f) =
      (quadraticSquareRootTwoTransport.ramificationIndex sqrtTwoUpperPlace : ℝ) *
        (finiteValueKernel (numberFieldGlobalPlaceData (F := ℚ))
          sqrtTwoRationalPlace).realification f := by
  have h := transportedFiniteValueKernel_realification_image
    quadraticSquareRootTwoTransport f sqrtTwoUpperPlace
  simpa [sqrtTwoRationalPlace] using h

end QuadraticValueTransport

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
