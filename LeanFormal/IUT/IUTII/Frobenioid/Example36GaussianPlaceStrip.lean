/-
  # The place-indexed local strip data of the Gaussian field Q(i)

  Task task-40 of the Group-1 split.  This module assembles, over the *actual*
  place index of the concrete Gaussian field Q(i), the local value data of the
  source prime strips that the repository can instantiate:

  * at every finite place v (a height-one prime of the ring of integers of
    Q(i)): the actual unit group of the v-adic completion as local value monoid,
    the actual classical valuation exponent as value-group coordinate, the
    actual residue-field cardinality as normalization constant, and the
    FrobenioidValueKernel on the value group (identity kernel on the value group,
    unit-level kernel on the completion units);
  * at every archimedean place w: the multiplicative real value group with the
    actual absolute-value coordinate -log (w .) and the archimedean
    FrobenioidValueKernel.

  The place index is the disjoint union of the finite places (height-one primes)
  and the archimedean places; it is proved equivalent to the repository's
  actual NumberFieldPlace carrier.

  ## What is proved (family level, new)

  * The local value group and its FrobenioidValueKernel are defined at every
    place (placeValueGroup, placeValueGroupKernel, placeValueGroupDegree,
    placeValueGroupRealification), with the finite and archimedean branches
    reducing definitionally to the prime-strip bridge data.
  * The value-group coordinate of a global unit at every place is proved equal
    to the Example 3.6 packaged place-data coordinate at that place
    (placeLocalValueOfGlobalUnit_eq_placeDataValue), and its realification is
    proved equal to the realified Example 3.6 place-data coordinate
    (placeLocalValueOfGlobalUnit_realification_eq_placeData).  This is the
    all-places identification of the prime-strip local data with the actual
    completion / absolute-value data.
  * At the concrete Gaussian place of Example36SourceTheaterCarrier the
    realified local value of a global unit is identified with (a) the finite
    coordinate of the Example 3.6 model-Frobenioid divisor input
    globalModelDivisor, (b) the finite coordinate of the principal-divisor
    family, and (c) the terminal-stage normalized additive valuation of the
    concrete stage model (the task-30 bridge), each read against the actual
    residue-field logarithm.

  ## What is NOT available (exact missing structure card)

  The value-group/degree layer above is all that the current tree can
  instantiate over the Gaussian places.  The paper's D-prime-strip additionally
  requires, at every place, the actual local absolute Galois group, its
  mono-analytic quotient, the projection, the geometric pi_1 kernel, and a
  Galois action on the local value monoid with the degree compatibility.  The
  tree contains no construction of the local absolute Galois groups of the
  places of Q(i), no mono-analytic quotients and no geometric pi_1 kernels at
  those places; the only concrete DPrimeStrip values in the tree are the
  identity-projection rational-prime finite-interval models
  (localDPrimeStrip, finiteLocalDPrimeStrip), whose projections are the identity
  and whose geometric kernels are therefore trivial (proved below).  These are
  not substituted for the source D-prime-strip here: they are only recorded,
  with their exact structure, as the existing model layer.  The frozen card
  GaussianPlaceDPrimeStripCard records the missing structure
  DPrimeStrip/Galois/pi_1 data as a specification; no inhabitant is constructed
  and no theorem below consumes one.  No identity-projection or constant-q model
  is substituted for the source data anywhere in this file.

  No theta-pilot, q-pilot, Tate, or further source-identification claim is made.

  Source correspondence: IUT I, Definition 5.2 (prime strips, places); IUT III,
  Example 3.6 (place-indexed local value data and model Frobenioid); IUT III,
  Remark 3.9.4 (value groups, log-shells).
-/

import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripBridge
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceTheaterCarrier
import LeanFormal.IUT.IUTII.Frobenioid.Example36StageNormalizationBridge
import LeanFormal.IUT.IUTI.HodgeTheater.LocalPrimePlaces
import LeanFormal.IUT.Foundations.NumberField.Places

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36
namespace GaussianPlaceStrip

open LeanFormal.IUT
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open Iut
open Iut.SourceFinitePlaceReconstruction
open IsDedekindDomain
open scoped NumberField

local instance gaussianPolynomialIrreducibleFactPlaceStrip :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance fivePrimeFactPlaceStrip : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

local instance primeFactPlaceStrip (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

noncomputable section

/-! ## 1. The actual place index of the Gaussian field -/

/-- The actual place index of the Gaussian field Q(i): finite places
(height-one primes of the ring of integers) and archimedean places. -/
abbrev GaussianPlaceIndex : Type :=
  HeightOneSpectrum (𝓞 GaussianField) ⊕ NumberField.InfinitePlace GaussianField

/-- The finite-place part of the place index. -/
def finiteGaussianPlace (v : HeightOneSpectrum (𝓞 GaussianField)) :
    GaussianPlaceIndex :=
  Sum.inl v

/-- The archimedean part of the place index. -/
def infiniteGaussianPlace (w : NumberField.InfinitePlace GaussianField) :
    GaussianPlaceIndex :=
  Sum.inr w

/-- The concrete place index of Example36SourceTheaterCarrier (the Gaussian
place above 5, as a height-one prime). -/
noncomputable def concreteGaussianPlace : GaussianPlaceIndex :=
  finiteGaussianPlace SourceTheaterCarrier.concreteHeightOneSpectrum

theorem concreteGaussianPlace_eq :
    concreteGaussianPlace =
      Sum.inl SourceTheaterCarrier.concreteHeightOneSpectrum :=
  rfl

/-- The place index is equivalent to the repository's actual full place carrier
NumberFieldPlace (finite and infinite places of a number field). -/
noncomputable def gaussianPlaceIndexEquiv :
    GaussianPlaceIndex ≃ NumberFieldPlace GaussianField where
  toFun P := match P with
    | Sum.inl v => NumberFieldPlace.finite (NumberField.FinitePlace.mk v)
    | Sum.inr w => NumberFieldPlace.infinite w
  invFun Q := match Q with
    | NumberFieldPlace.finite p => Sum.inl p.maximalIdeal
    | NumberFieldPlace.infinite w => Sum.inr w
  left_inv P := by
    cases P with
    | inl v => simp only [NumberField.FinitePlace.maximalIdeal_mk]
    | inr w => rfl
  right_inv Q := by
    cases Q with
    | finite p => exact congrArg NumberFieldPlace.finite (NumberField.FinitePlace.mk_maximalIdeal p)
    | infinite w => rfl

/-! ## 2. The local value group and its degree kernel at every place -/

/-- The local value group (in multiplicative notation) at a place of the
Gaussian field: the integers at a finite place, the reals at an archimedean
place. -/
def placeValueGroup (P : GaussianPlaceIndex) : Type :=
  match P with
  | Sum.inl _ => finitePlaceValueGroup
  | Sum.inr _ => archimedeanValueGroup

instance (P : GaussianPlaceIndex) : CommMonoid (placeValueGroup P) := by
  cases P with
  | inl _ => exact inferInstanceAs (CommMonoid finitePlaceValueGroup)
  | inr _ => exact inferInstanceAs (CommMonoid archimedeanValueGroup)

/-- The FrobenioidValueKernel on the local value group at a place: the finite
value-group degree kernel (residue-field normalization) at a finite place, the
archimedean identity-degree kernel at an archimedean place. -/
noncomputable def placeValueGroupKernel (P : GaussianPlaceIndex) :
    FrobenioidValueKernel (placeValueGroup P) :=
  match P with
  | Sum.inl v => finitePlaceValueGroupKernel (F := GaussianField) v
  | Sum.inr _ => archimedeanValueGroupKernel

/-- The degree map of the local value-group kernel at a place. -/
noncomputable def placeValueGroupDegree (P : GaussianPlaceIndex) :
    placeValueGroup P →* Multiplicative ℝ :=
  (placeValueGroupKernel P).degree

/-- The realification of the local value-group kernel at a place. -/
noncomputable def placeValueGroupRealification (P : GaussianPlaceIndex) :
    placeValueGroup P → ℝ :=
  (placeValueGroupKernel P).realification

@[simp] theorem placeValueGroupKernel_finite
    (v : HeightOneSpectrum (𝓞 GaussianField)) :
    placeValueGroupKernel (finiteGaussianPlace v) =
      finitePlaceValueGroupKernel (F := GaussianField) v :=
  rfl

@[simp] theorem placeValueGroupKernel_infinite
    (w : NumberField.InfinitePlace GaussianField) :
    placeValueGroupKernel (infiniteGaussianPlace w) =
      archimedeanValueGroupKernel :=
  rfl

@[simp] theorem placeValueGroupDegree_finite
    (v : HeightOneSpectrum (𝓞 GaussianField)) :
    placeValueGroupDegree (finiteGaussianPlace v) =
      finitePlaceValueGroupDegree (F := GaussianField) v :=
  rfl

@[simp] theorem placeValueGroupDegree_infinite
    (w : NumberField.InfinitePlace GaussianField) :
    placeValueGroupDegree (infiniteGaussianPlace w) =
      MonoidHom.id archimedeanValueGroup :=
  rfl

@[simp] theorem placeValueGroupRealification_finite
    (v : HeightOneSpectrum (𝓞 GaussianField)) :
    placeValueGroupRealification (finiteGaussianPlace v) =
      (finitePlaceValueGroupKernel (F := GaussianField) v).realification :=
  rfl

@[simp] theorem placeValueGroupRealification_infinite
    (w : NumberField.InfinitePlace GaussianField) :
    placeValueGroupRealification (infiniteGaussianPlace w) =
      archimedeanValueGroupKernel.realification :=
  rfl

/-! ## 3. The finite-place unit-level local value monoid -/

/-- The finite-place local value monoid at the unit level: the unit group of the
actual v-adic completion of the Gaussian field. -/
abbrev placeUnitValueMonoid (v : HeightOneSpectrum (𝓞 GaussianField)) : Type :=
  finitePlaceUnitValueMonoid (F := GaussianField) v

/-- The unit-level finite-place value kernel of the prime strip. -/
noncomputable def placeUnitValueKernel (v : HeightOneSpectrum (𝓞 GaussianField)) :
    FrobenioidValueKernel (placeUnitValueMonoid v) :=
  finitePlaceUnitValueKernel (F := GaussianField) v

/-- The value-group coordinate at a finite place (classical exponent). -/
noncomputable def placeUnitLocalValue (v : HeightOneSpectrum (𝓞 GaussianField)) :
    placeUnitValueMonoid v →* placeValueGroup (finiteGaussianPlace v) :=
  finitePlaceLocalValue (F := GaussianField) v

/-- The normalized local log-volume degree at a finite place. -/
noncomputable def placeUnitLocalDegree (v : HeightOneSpectrum (𝓞 GaussianField)) :
    placeUnitValueMonoid v →* Multiplicative ℝ :=
  finitePlaceLocalDegree (F := GaussianField) v

/-- The embedding of global units of the Gaussian field into the completion
units at a finite place. -/
noncomputable def placeUnitGlobalUnitValue
    (v : HeightOneSpectrum (𝓞 GaussianField)) :
    GaussianFieldˣ →* placeUnitValueMonoid v :=
  finitePlaceGlobalUnitValue (F := GaussianField) v

/-! ## 4. The local value of a global unit at every place -/

/-- The prime-strip local value-group coordinate of a global unit at a place:
the classical exponent of the embedded completion unit at a finite place, the
actual archimedean absolute-value coordinate -log (w .) at an archimedean
place. -/
noncomputable def placeLocalValueOfGlobalUnit (P : GaussianPlaceIndex)
    (f : GaussianFieldˣ) : placeValueGroup P :=
  match P with
  | Sum.inl v => placeUnitLocalValue v (placeUnitGlobalUnitValue v f)
  | Sum.inr w => archimedeanPlaceValueUnit (F := GaussianField) w f

/-- The Example 3.6 packaged place-data value of a global unit at a place. -/
noncomputable def example36PlaceDataValue (P : GaussianPlaceIndex)
    (f : GaussianFieldˣ) : placeValueGroup P :=
  match P with
  | Sum.inl v =>
      Multiplicative.ofAdd
        ((numberFieldGlobalPlaceData (F := GaussianField)).finiteDelta f v)
  | Sum.inr w =>
      Multiplicative.ofAdd
        ((numberFieldGlobalPlaceData (F := GaussianField)).infiniteDelta f w)

/-- The realified Example 3.6 place-data coordinate of a global unit at a
place: the normalized finite log-volume -nu log #(O/v) at a finite place, the
archimedean coordinate infiniteDelta at an archimedean place. -/
noncomputable def example36PlaceDataRealified (P : GaussianPlaceIndex)
    (f : GaussianFieldˣ) : ℝ :=
  match P with
  | Sum.inl v =>
      -(((numberFieldGlobalPlaceData (F := GaussianField)).finiteDelta f v : ℤ) : ℝ) *
        Real.log ((finitePlaceResidueCardinality (F := GaussianField) v : ℕ) : ℝ)
  | Sum.inr w =>
      (numberFieldGlobalPlaceData (F := GaussianField)).infiniteDelta f w

@[simp] theorem placeLocalValueOfGlobalUnit_finite
    (v : HeightOneSpectrum (𝓞 GaussianField)) (f : GaussianFieldˣ) :
    placeLocalValueOfGlobalUnit (finiteGaussianPlace v) f =
      placeUnitLocalValue v (placeUnitGlobalUnitValue v f) :=
  rfl

@[simp] theorem placeLocalValueOfGlobalUnit_infinite
    (w : NumberField.InfinitePlace GaussianField) (f : GaussianFieldˣ) :
    placeLocalValueOfGlobalUnit (infiniteGaussianPlace w) f =
      archimedeanPlaceValueUnit (F := GaussianField) w f :=
  rfl

/-- **Value-group identification at every place.**  The prime-strip local
value-group coordinate of a global unit at any place is the Example 3.6 packaged
place-data value at that place (finite: the classical v-adic exponent; infinite:
-log of the archimedean absolute value). -/
theorem placeLocalValueOfGlobalUnit_eq_placeDataValue (P : GaussianPlaceIndex)
    (f : GaussianFieldˣ) :
    placeLocalValueOfGlobalUnit P f = example36PlaceDataValue P f := by
  cases P with
  | inl v =>
      change finitePlaceLocalValue (F := GaussianField) v
          (finitePlaceGlobalUnitValue (F := GaussianField) v f) =
        Multiplicative.ofAdd
          ((numberFieldGlobalPlaceData (F := GaussianField)).finiteDelta f v)
      rw [finitePlaceLocalValue_apply, finitePlaceGlobalUnitValue_exponent,
        ← numberFieldGlobalPlaceData_finiteDelta]
  | inr w =>
      change archimedeanPlaceValueUnit (F := GaussianField) w f =
        Multiplicative.ofAdd
          ((numberFieldGlobalPlaceData (F := GaussianField)).infiniteDelta f w)
      rw [archimedeanPlaceValueUnit_apply,
        numberFieldGlobalPlaceData_infiniteDelta]
      simp only [archimedeanPlaceValue]

/-- **All-places identification with the actual completion / absolute-value
data.**  The realification of the prime-strip local value of a global unit at
any place is the realified Example 3.6 place-data coordinate at that place. -/
theorem placeLocalValueOfGlobalUnit_realification_eq_placeData
    (P : GaussianPlaceIndex) (f : GaussianFieldˣ) :
    placeValueGroupRealification P (placeLocalValueOfGlobalUnit P f) =
      example36PlaceDataRealified P f := by
  cases P with
  | inl v =>
      change (finitePlaceValueGroupKernel (F := GaussianField) v).realification
          (finitePlaceLocalValue (F := GaussianField) v
            (finitePlaceGlobalUnitValue (F := GaussianField) v f)) =
        -(((numberFieldGlobalPlaceData (F := GaussianField)).finiteDelta f v : ℤ) : ℝ) *
          Real.log ((finitePlaceResidueCardinality (F := GaussianField) v : ℕ) : ℝ)
      rw [finitePlaceValueGroupKernel_realification, finitePlaceLocalValue_apply,
        toAdd_ofAdd, finitePlaceGlobalUnitValue_exponent,
        ← numberFieldGlobalPlaceData_finiteDelta]
  | inr w =>
      change archimedeanValueGroupKernel.realification
          (archimedeanPlaceValueUnit (F := GaussianField) w f) =
        (numberFieldGlobalPlaceData (F := GaussianField)).infiniteDelta f w
      exact archimedeanValueGroupKernel_realification_infiniteDelta
        (F := GaussianField) w f

/-! ## 5. The concrete Gaussian place of Example36SourceTheaterCarrier -/

theorem concreteHeightOneSpectrum_eq_underlyingPrime :
    SourceTheaterCarrier.concreteHeightOneSpectrum =
      underlyingPrime concretePlace :=
  rfl

/-- The finite coordinate of the Example 3.6 model-Frobenioid divisor input at
the concrete place, as an integer. -/
noncomputable def concretePlaceBackendCoordinate (f : GaussianFieldˣ) : ℤ :=
  ((SourceModelBackend.coneGrothendieckEquiv (F := GaussianField))
    ((SourceModelBackend.globalModelDivisor (F := GaussianField))
      (Additive.ofMul f))).1
        SourceTheaterCarrier.concreteHeightOneSpectrum

/-- The finite coordinate of the principal-divisor family at the concrete
place, as an integer. -/
noncomputable def concretePlacePrincipalCoordinate (f : GaussianFieldˣ) : ℤ :=
  (sourceModelPrincipalDivisor (numberFieldGlobalPlaceData (F := GaussianField))
    numberFieldGlobalPlaceData_hasFiniteSupport f).finite
      SourceTheaterCarrier.concreteHeightOneSpectrum

/-- The terminal-stage normalized additive valuation of the task-30 concrete
stage model of the global unit, as an integer. -/
noncomputable def concretePlaceStageCoordinate (f : GaussianFieldˣ) : ℤ :=
  stageNormalizedAdditiveValuation concretePlace (⊥ : StageIndex concretePlace)
    (Additive.ofMul
      (StageNormalizationBridge.globalUnitToBottomUnit concretePlace f))

/-- At the concrete Gaussian place, the realified prime-strip local value is the
finite coordinate of the Example 3.6 model-Frobenioid divisor input
globalModelDivisor, read against the actual residue-field logarithm. -/
theorem concreteGaussianPlace_backend_agreement (f : GaussianFieldˣ) :
    placeValueGroupRealification concreteGaussianPlace
        (placeLocalValueOfGlobalUnit concreteGaussianPlace f) =
      -((concretePlaceBackendCoordinate f : ℤ) : ℝ) *
          Real.log ((finitePlaceResidueCardinality (F := GaussianField)
            SourceTheaterCarrier.concreteHeightOneSpectrum : ℕ) : ℝ) := by
  rw [placeLocalValueOfGlobalUnit_realification_eq_placeData]
  simp only [concreteGaussianPlace, finiteGaussianPlace, example36PlaceDataRealified,
    concretePlaceBackendCoordinate]
  rw [SourceTheaterCarrier.example36PlaceData_finiteDelta_concretePlace,
    ← SourceTheaterCarrier.example36Backend_divisor_finite_coordinate]

/-- At the concrete Gaussian place, the realified prime-strip local value is the
finite coordinate of the principal-divisor family of the global unit, read
against the actual residue-field logarithm. -/
theorem concreteGaussianPlace_principalDivisor_agreement (f : GaussianFieldˣ) :
    placeValueGroupRealification concreteGaussianPlace
        (placeLocalValueOfGlobalUnit concreteGaussianPlace f) =
      -((concretePlacePrincipalCoordinate f : ℤ) : ℝ) *
          Real.log ((finitePlaceResidueCardinality (F := GaussianField)
            SourceTheaterCarrier.concreteHeightOneSpectrum : ℕ) : ℝ) := by
  rw [placeLocalValueOfGlobalUnit_realification_eq_placeData]
  simp only [concreteGaussianPlace, finiteGaussianPlace, example36PlaceDataRealified,
    concretePlacePrincipalCoordinate]
  rw [sourceModelPrincipalDivisor_finite_apply,
    SourceTheaterCarrier.example36PlaceData_finiteDelta_concretePlace]

/-- At the concrete Gaussian place, the realified prime-strip local value is
minus the terminal-stage normalized additive valuation of the task-30 concrete
stage model, times the residue-field logarithm. -/
theorem concreteGaussianPlace_stageValuation_agreement (f : GaussianFieldˣ) :
    placeValueGroupRealification concreteGaussianPlace
        (placeLocalValueOfGlobalUnit concreteGaussianPlace f) =
      -((concretePlaceStageCoordinate f : ℤ) : ℝ) *
          Real.log ((finitePlaceResidueCardinality (F := GaussianField)
            SourceTheaterCarrier.concreteHeightOneSpectrum : ℕ) : ℝ) := by
  rw [placeLocalValueOfGlobalUnit_realification_eq_placeData]
  simp only [concreteGaussianPlace, finiteGaussianPlace, example36PlaceDataRealified,
    concretePlaceStageCoordinate]
  rw [SourceTheaterCarrier.example36PlaceData_finiteDelta_concretePlace,
    concreteHeightOneSpectrum_eq_underlyingPrime,
    ← StageNormalizationBridge.stageNormalizedAdditiveValuation_bot_globalUnit
        concretePlace f]

/-! ## 6. The existing identity-projection D-strip models and the missing card -/

/-- The concrete rational-prime D-strip model of the tree has identity
projection. -/
theorem localDPrimeStrip_proj_id (v : RationalPrimePlace) :
    localDPrimeStrip.proj v = MonoidHom.id (localDPrimeStrip.Pi v) :=
  rfl

/-- The concrete rational-prime D-strip model has trivial geometric kernel: it
carries no geometric pi_1 data.  It is the value-side model of the tree, not the
source D-prime-strip. -/
theorem localDPrimeStrip_geometric_eq_bot (v : RationalPrimePlace) :
    localDPrimeStrip.geometric v = ⊥ := by
  rw [DPrimeStrip.geometric, localDPrimeStrip_proj_id]
  exact MonoidHom.ker_id

/-- The finite-interval D-strip model of the tree has identity projection. -/
theorem finiteLocalDPrimeStrip_proj_id (lower upper : ℕ)
    (v : FinitePrimePlace lower upper) :
    (finiteLocalDPrimeStrip lower upper).proj v =
      MonoidHom.id ((finiteLocalDPrimeStrip lower upper).Pi v) :=
  rfl

/-- The finite-interval D-strip model has trivial geometric kernel. -/
theorem finiteLocalDPrimeStrip_geometric_eq_bot (lower upper : ℕ)
    (v : FinitePrimePlace lower upper) :
    (finiteLocalDPrimeStrip lower upper).geometric v = ⊥ := by
  rw [DPrimeStrip.geometric, finiteLocalDPrimeStrip_proj_id]
  exact MonoidHom.ker_id

/-- **Frozen specification card for the missing D-prime-strip / Galois /
geometric pi_1 structure over the Gaussian field.**  This records exactly the
data that the source would have to supply at every place of Q(i): the local
absolute Galois group, its mono-analytic quotient, the surjective projection,
the geometric pi_1 kernel, and the action on the local value monoid with the
degree map.  No inhabitant is constructed in this file and no theorem below
consumes one; the value-group/degree layer of this file is not claimed to be a
D-prime-strip.  In particular no identity-projection model is substituted for
this structure. -/
structure GaussianPlaceDPrimeStripCard where
  /-- The local absolute Galois group at each place. -/
  Pi : GaussianPlaceIndex → Type
  /-- The group structure on the local absolute Galois group. -/
  [groupPi : ∀ P, Group (Pi P)]
  /-- The mono-analytic quotient at each place. -/
  G : GaussianPlaceIndex → Type
  /-- The group structure on the mono-analytic quotient. -/
  [groupG : ∀ P, Group (G P)]
  /-- The projection from the local absolute Galois group to its quotient. -/
  proj : ∀ P, Pi P →* G P
  /-- The projection is surjective. -/
  proj_surjective : ∀ P, Function.Surjective (proj P)
  /-- The local value monoid at each place. -/
  Mon : GaussianPlaceIndex → Type
  /-- The commutative monoid structure on the local value monoid. -/
  [commMonoidMon : ∀ P, CommMonoid (Mon P)]
  /-- The action of the local absolute Galois group on the value monoid. -/
  action : ∀ P, Pi P →* MulAut (Mon P)
  /-- The local degree map of the value monoid. -/
  degree : ∀ P, Mon P →* Multiplicative ℝ

/-! ## 7. Summary -/

/-- **Summary of the place-indexed local strip data.**  At every place of the
Gaussian field the local value group, its degree kernel and the local value of
global units are constructed from the actual completion / absolute-value data;
the value-group coordinate and its realification agree with the Example 3.6
place data at that place; at the concrete Gaussian place the realified value
agrees with the backend model-Frobenioid divisor coordinate, the
principal-divisor coordinate, and the terminal-stage normalized additive
valuation.  The existing D-strip models have identity projection and trivial
geometric kernel; the missing D-prime-strip/Galois/pi_1 structure is frozen as
GaussianPlaceDPrimeStripCard. -/
theorem gaussianPlaceStrip_data_summary (f : GaussianFieldˣ) :
    (placeLocalValueOfGlobalUnit concreteGaussianPlace f =
      example36PlaceDataValue concreteGaussianPlace f) ∧
    (placeValueGroupRealification concreteGaussianPlace
        (placeLocalValueOfGlobalUnit concreteGaussianPlace f) =
      example36PlaceDataRealified concreteGaussianPlace f) ∧
    (placeValueGroupRealification concreteGaussianPlace
        (placeLocalValueOfGlobalUnit concreteGaussianPlace f) =
      -((concretePlaceBackendCoordinate f : ℤ) : ℝ) *
          Real.log ((finitePlaceResidueCardinality (F := GaussianField)
            SourceTheaterCarrier.concreteHeightOneSpectrum : ℕ) : ℝ)) :=
  ⟨placeLocalValueOfGlobalUnit_eq_placeDataValue concreteGaussianPlace f,
    placeLocalValueOfGlobalUnit_realification_eq_placeData concreteGaussianPlace f,
    concreteGaussianPlace_backend_agreement f⟩

end

end GaussianPlaceStrip
end Example36
end Frobenioid
end IUTII
end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the place-indexed local strip data of the Gaussian field.
The actual local value data at all finite and archimedean places of Q(i) is
assembled and identified with the completion/absolute-value data and with the
Example 3.6 place data; the missing D-prime-strip/Galois/pi_1 structure is
recorded as a frozen card (GaussianPlaceDPrimeStripCard) and the existing
identity-projection D-strip models are recorded with their trivial geometric
kernels. -/
def example36GaussianPlaceStrip : Obligation :=
  { id := "IUT-II.example36-gaussian-place-strip"
    source :=
      "IUT I, Definition 5.2 (prime strips and places); IUT III, Example 3.6 " ++
        "(place-indexed local value data and model Frobenioid); IUT III, " ++
        "Remark 3.9.4 (value groups and log-shells)"
    status := VerificationStatus.interface
    note :=
      "Constructed the actual place index of Q(i) (finite height-one primes " ++
        "plus archimedean places), proved it equivalent to the repository's " ++
        "NumberFieldPlace carrier (gaussianPlaceIndexEquiv), and assembled at " ++
        "every place the local value group (integers at finite places, reals at " ++
        "archimedean places), its FrobenioidValueKernel (finite value-group " ++
        "degree kernel with residue-field normalization; archimedean identity " ++
        "degree kernel), the degree map and the realification " ++
        "(placeValueGroup, placeValueGroupKernel, placeValueGroupDegree, " ++
        "placeValueGroupRealification). At finite places the actual completion " ++
        "unit group, unit-level kernel, classical-exponent value map, normalized " ++
        "log-volume degree and global-unit embedding are assembled " ++
        "(placeUnitValueMonoid, placeUnitValueKernel, placeUnitLocalValue, " ++
        "placeUnitLocalDegree, placeUnitGlobalUnitValue). Proved the all-places " ++
        "identifications: the value-group coordinate of a global unit equals the " ++
        "Example 3.6 packaged place-data value at that place " ++
        "(placeLocalValueOfGlobalUnit_eq_placeDataValue) and its realification " ++
        "equals the realified Example 3.6 place-data coordinate " ++
        "(placeLocalValueOfGlobalUnit_realification_eq_placeData), i.e. the " ++
        "actual completion/absolute-value data. At the concrete Gaussian place " ++
        "of Example36SourceTheaterCarrier the realified local value is identified " ++
        "with the model-Frobenioid divisor coordinate " ++
        "(concreteGaussianPlace_backend_agreement), the principal-divisor " ++
        "coordinate (concreteGaussianPlace_principalDivisor_agreement), and the " ++
        "terminal-stage normalized additive valuation of the task-30 stage model " ++
        "(concreteGaussianPlace_stageValuation_agreement). NOT available and " ++
        "frozen as the card GaussianPlaceDPrimeStripCard: at every place the " ++
        "actual local absolute Galois group, its mono-analytic quotient, the " ++
        "surjective projection, the geometric pi_1 kernel, the Galois action on " ++
        "the local value monoid and the degree compatibility are not constructed " ++
        "in the tree; no local absolute Galois groups at the places of Q(i) and no " ++
        "mono-analytic quotients exist. The only concrete DPrimeStrip values in " ++
        "the tree are the identity-projection rational-prime finite-interval " ++
        "models localDPrimeStrip and finiteLocalDPrimeStrip, whose geometric " ++
        "kernels are proved trivial (localDPrimeStrip_geometric_eq_bot, " ++
        "finiteLocalDPrimeStrip_geometric_eq_bot); they are recorded, not " ++
        "substituted. No identity or constant-q substitution is made, and no " ++
        "theta-pilot/q-pilot/Tate claim is added."
    dependsOn :=
      [ "IUT-I-II.source-finite-stage-model-frobenioid",
        "IUT-II.local-integral-f-prime-strip-carrier",
        "IUT-II.example36-stage-normalization-bridge",
        "IUT-II.example36-source-theater-carrier",
        "IUT-I-II.prime-strips-frobenioids" ] }

end LeanFormal.IUT.Audit
