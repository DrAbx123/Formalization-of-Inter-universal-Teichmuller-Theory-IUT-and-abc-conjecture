/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal IUT/ABC contributors
-/
import LeanFormal.IUT.IUTII.Frobenioid.Example36NumberFieldPlaceCompletionBridge
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelBackend
import LeanFormal.IUT.IUTII.Frobenioid.PrimeStripFrobenioidCategorySkeleton

set_option linter.unusedSectionVars false

/-!
# The prime-strip value monoid and degree kernel of III Example 3.6

This module builds the value-monoid layer of the source prime strips at the
places of a number field F out of the actual number-field place data, and
proves that its degree and realification coordinates agree with the local
value data of IUT III, Example 3.6 (the LocalValueData of
Example36LocalValueData.lean and the place-indexed GlobalPlaceData of
Example36NumberFieldPlaceData.lean), and with the divisor coordinates of the
model-Frobenioid input of Example36SourceModelBackend.lean.

The content has four steps.

1. At a finite place v (a height-one prime of the ring of integers of F), the
   source local value monoid Gamma_v = K_v^! / U_v is the value group of the
   actual v-adic completion, i.e. the integers in multiplicative notation.
   The actual arithmetic object is the unit group of the completion
   v.adicCompletion F; the classical exponent completionValuationExponent v
   is its value coordinate.  Its kernel is exactly the group of integral units
   O_v^x, and it is surjective onto the integers, so the quotient by the
   kernel is the value group.  The normalized local log-volume degree reads
   the exponent against the logarithm of the actual residue-field
   cardinality #(O_F / v): a completion unit of exponent nu has degree
   -nu * log #(O_F / v), which is the logarithm of the normalized absolute
   value |x|_v = (#(O_F / v))^(-nu) of the local field.  The degree kernel on
   the value group is trivial (the degree map is injective), and the degree
   kernel on the completion units is the group O_v^x of integral units.

2. The archimedean value monoid at an infinite place w is the real line in
   multiplicative notation, with the actual local principal value
   -log (w f) of a global unit.  The degree map is the identity on the value
   group, so the realification of the archimedean principal value is exactly
   -log (w f).

3. The Frobenius power dynamics of the prime strips (the value side of item
   (4) of the frozen boundary, valueFrobeniusPower of
   PrimeStripFrobenioidCategorySkeleton.lean) is shown to be compatible with
   the Example 3.6 exponents: the realified degree of the n-th Frobenius
   power is n times the realified degree of the value, on the finite value
   group, on the completion units, and on the archimedean value monoid; and
   the finite-place degree of the embedded global unit f^n is n times the
   finite-place degree of f, matching GlobalPlaceData.finiteDelta_pow.

4. The prime-strip local values are identified with the divisor coordinates
   of the model-Frobenioid input numberFieldSourceModelInput of
   Example36SourceModelBackend.lean: the finite coordinate of the input
   divisor map is the completion exponent of the embedded global unit (equal
   to finitePlaceValueExponent), and the archimedean coordinate is
   -log (w f) (equal to the infiniteDelta of the global place data).

Boundary, stated precisely.  This file constructs the value-monoid and
degree-kernel layer only.  It does not construct the D-prime-strip side of
the source prime strips (the projection to the absolute Galois group and the
geometric kernel pi_1^geo; the current concrete local strips have identity
projection, so their geometric kernel is trivial, see the boundary item (1)
of PrimeStripsConstruction.lean and geometricPiOneBoundary), the categorical
Frobenioid C_v / C_vdash / C_mod (card CAT), the V_K transport and rho_v
normalization (boundary item (2)), the divisor-side and log-shell
compatibility of the arithmetic Frobenius (boundary item (4)), or any Hodge
theater, theta-pilot, q-pilot or Tate-uniformization object.  The reduced
FrobenioidValueKernel record used here is the consumer shape of
PrimeStripsFrobenioidLinks.lean; its effective field is total in this reduced
form and is not the integral cone of the source (the integral cones are those
of the LocalValueData fields, and the compatibility of the local values with
them is the local-inclusion theorem of Example36NumberFieldPlaceData.lean).
No map from the local value group back to the global units is constructed:
no such section exists in the source, so only the mod (global-to-local)
direction is formalized.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open LeanFormal.IUT (FrobenioidValueKernel valueFrobeniusPower
  valueFrobeniusPower_degree valueFrobeniusPower_realification)
open IsDedekindDomain NumberField
open scoped NumberField

universe u

variable {F : Type u} [Field F] [NumberField F]

/-! ## 1. The residue-field cardinality of a finite place -/

/-- The cardinality of the actual residue field O_F / v of the finite place v,
read off from the finite quotient of the Dedekind domain.  This is the
normalization factor of the local log-volume at v: a completion unit of
classical exponent nu has normalized absolute value q_v^(-nu), where q_v is
this cardinality. -/
noncomputable def finitePlaceResidueCardinality (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  Nat.card (𝓞 F ⧸ v.asIdeal)

/-- The residue field of a finite place is finite. -/
theorem finitePlaceResidueField_finite (v : HeightOneSpectrum (𝓞 F)) :
    Finite (𝓞 F ⧸ v.asIdeal) :=
  v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot

/-- The residue-field cardinality of a finite place is positive. -/
theorem finitePlaceResidueCardinality_pos (v : HeightOneSpectrum (𝓞 F)) :
    0 < finitePlaceResidueCardinality (F := F) v := by
  classical
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := finitePlaceResidueField_finite (F := F) v
  exact Nat.card_pos

/-- The residue-field cardinality of a finite place is greater than one: the
residue field contains the distinct elements 0 and 1. -/
theorem finitePlaceResidueCardinality_gt_one (v : HeightOneSpectrum (𝓞 F)) :
    1 < finitePlaceResidueCardinality (F := F) v := by
  classical
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := finitePlaceResidueField_finite (F := F) v
  haveI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  rw [finitePlaceResidueCardinality, Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

/-- The logarithm of the residue-field cardinality is positive; it is the
normalization constant of the finite-place degree. -/
theorem finitePlaceResidueCardinality_log_pos (v : HeightOneSpectrum (𝓞 F)) :
    0 < Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) := by
  apply Real.log_pos
  exact_mod_cast finitePlaceResidueCardinality_gt_one (F := F) v

/-- The logarithm of the residue-field cardinality is nonzero. -/
theorem finitePlaceResidueCardinality_log_ne_zero (v : HeightOneSpectrum (𝓞 F)) :
    Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) ≠ 0 :=
  ne_of_gt (finitePlaceResidueCardinality_log_pos (F := F) v)

/-- The normalized log-volume scale is injective on integer exponents: for a
fixed finite place, the real number -(e) * log #(O_F / v) vanishes exactly at
e = 0. -/
theorem finitePlaceResidueCardinality_neg_mul_log_eq_zero_iff
    (v : HeightOneSpectrum (𝓞 F)) (e : ℤ) :
    -(e : ℝ) * Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) = 0 ↔ e = 0 := by
  constructor
  · intro h
    have hprod : (e : ℝ) *
        Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) = 0 := by
      rw [neg_mul] at h
      exact neg_eq_zero.mp h
    rcases mul_eq_zero.mp hprod with h1 | h2
    · exact Int.cast_injective (α := ℝ) (by simpa using h1)
    · exact absurd h2 (finitePlaceResidueCardinality_log_ne_zero (F := F) v)
  · intro h
    rw [h]
    simp

/-! ## 2. The value monoid of a finite place and its degree -/

/-- The value-group-level local value monoid of the prime strip at a finite
place: the value group of the actual v-adic completion, written in
multiplicative notation.  It is the integers additively. -/
abbrev finitePlaceValueGroup : Type := Multiplicative ℤ

/-- The unit-level lift of the local value monoid: the unit group of the
actual v-adic completion.  Its quotient by the integral units O_v^x is the
value group Gamma_v. -/
abbrev finitePlaceUnitValueMonoid (v : HeightOneSpectrum (𝓞 F)) : Type u :=
  (v.adicCompletion F)ˣ

/-- The value-group coordinate of a unit of the actual completion: the
classical exponent nu_v, as a monoid homomorphism into the value group
(multiplicative notation). -/
noncomputable def finitePlaceLocalValue (v : HeightOneSpectrum (𝓞 F)) :
    finitePlaceUnitValueMonoid (F := F) v →* finitePlaceValueGroup :=
  completionValuationExponentMonoidHom v

/-- The value-group coordinate of a completion unit is its classical
exponent. -/
@[simp]
theorem finitePlaceLocalValue_apply (v : HeightOneSpectrum (𝓞 F))
    (x : finitePlaceUnitValueMonoid (F := F) v) :
    finitePlaceLocalValue (F := F) v x =
      Multiplicative.ofAdd (completionValuationExponent v x) :=
  rfl

/-- The value-group coordinate is surjective: the local value group at a
finite place is all of the integers. -/
theorem finitePlaceLocalValue_surjective (v : HeightOneSpectrum (𝓞 F)) :
    Function.Surjective (finitePlaceLocalValue (F := F) v) := by
  intro n
  obtain ⟨x, hx⟩ := completionValuationExponent_surjective (K := F) v (Multiplicative.toAdd n)
  refine ⟨x, ?_⟩
  rw [finitePlaceLocalValue_apply, hx, ofAdd_toAdd]

/-- The kernel of the value-group coordinate is exactly the group O_v^x of
integral units of the completion: the value monoid K_v^! / U_v is the
quotient of the completion units by the integral units. -/
theorem finitePlaceLocalValue_eq_one_iff_mem_integralUnits
    (v : HeightOneSpectrum (𝓞 F)) (x : finitePlaceUnitValueMonoid (F := F) v) :
    finitePlaceLocalValue (F := F) v x = 1 ↔
      x ∈ (v.adicCompletionIntegers F).units := by
  rw [finitePlaceLocalValue_apply, ofAdd_eq_one,
    completionValuationExponent_eq_zero_iff_mem_integralUnits]

/-- The normalized local log-volume degree at a finite place: a completion
unit of exponent nu has degree -nu * log #(O_F / v), i.e. the logarithm of
its normalized absolute value |x|_v = (#(O_F / v))^(-nu) in the local field.
This is the degree map of the source F-prime-strip at the finite place. -/
noncomputable def finitePlaceLocalDegree (v : HeightOneSpectrum (𝓞 F)) :
    finitePlaceUnitValueMonoid (F := F) v →* Multiplicative ℝ where
  toFun x := Multiplicative.ofAdd
    (-(completionValuationExponent v x : ℝ) *
      Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)))
  map_one' := by
    simp
  map_mul' := by
    intro x y
    rw [completionValuationExponent_mul]
    push_cast
    rw [← ofAdd_add]
    congr 1
    ring

/-- The finite-place degree of a completion unit is the normalized log-volume
of its exponent. -/
@[simp]
theorem finitePlaceLocalDegree_apply (v : HeightOneSpectrum (𝓞 F))
    (x : finitePlaceUnitValueMonoid (F := F) v) :
    finitePlaceLocalDegree (F := F) v x = Multiplicative.ofAdd
      (-(completionValuationExponent v x : ℝ) *
        Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ))) :=
  rfl

/-- The degree of the prime-strip value at a finite place, on the value group:
a value of exponent n has degree -n * log #(O_F / v). -/
noncomputable def finitePlaceValueGroupDegree (v : HeightOneSpectrum (𝓞 F)) :
    finitePlaceValueGroup →* Multiplicative ℝ where
  toFun n := Multiplicative.ofAdd
    (-((Multiplicative.toAdd n : ℤ) : ℝ) *
      Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)))
  map_one' := by
    simp
  map_mul' := by
    intro x y
    rw [toAdd_mul]
    push_cast
    rw [← ofAdd_add]
    congr 1
    ring

/-- The value-group degree of a value of exponent n is the normalized
log-volume of n. -/
@[simp]
theorem finitePlaceValueGroupDegree_apply (v : HeightOneSpectrum (𝓞 F))
    (n : finitePlaceValueGroup) :
    finitePlaceValueGroupDegree (F := F) v n = Multiplicative.ofAdd
      (-((Multiplicative.toAdd n : ℤ) : ℝ) *
        Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ))) :=
  rfl

/-- The value-group degree is the finite-place degree after taking the value
coordinate: the unit-level and value-group-level degrees agree. -/
theorem finitePlaceLocalDegree_factorization (v : HeightOneSpectrum (𝓞 F)) :
    finitePlaceLocalDegree (F := F) v =
      (finitePlaceValueGroupDegree (F := F) v).comp
        (finitePlaceLocalValue (F := F) v) := by
  ext x
  simp [finitePlaceLocalDegree, finitePlaceValueGroupDegree, finitePlaceLocalValue]

/-! ## 3. The degree kernels at a finite place -/

/-- The degree kernel of the prime strip at a finite place, at the unit level:
the FrobenioidValueKernel on the completion units whose degree is the
normalized local log-volume and whose realification is the additive form of
that degree.  This is the local value kernel consumed by the Frobenioid
link-layer contract of PrimeStripsFrobenioidLinks.lean. -/
noncomputable def finitePlaceUnitValueKernel (v : HeightOneSpectrum (𝓞 F)) :
    FrobenioidValueKernel (finitePlaceUnitValueMonoid (F := F) v) where
  degree := finitePlaceLocalDegree (F := F) v
  realification := fun x =>
    -(completionValuationExponent v x : ℝ) *
      Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ))
  realification_mul := by
    intro x y
    rw [completionValuationExponent_mul]
    push_cast
    ring
  degree_realification := by
    intro x
    rfl
  unit := 1
  unit_realification := by
    simp
  effective := fun _ => True
  effective_proved := fun _ => trivial
  transport := id
  transport_degree := by
    intro x
    rfl

/-- The realification of the unit-level finite-place degree kernel is the
negated classical exponent times the residue-field logarithm. -/
@[simp]
theorem finitePlaceUnitValueKernel_realification (v : HeightOneSpectrum (𝓞 F))
    (x : finitePlaceUnitValueMonoid (F := F) v) :
    (finitePlaceUnitValueKernel (F := F) v).realification x =
      -(completionValuationExponent v x : ℝ) *
        Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) :=
  rfl

/-- The realification of the finite-place degree, in the logarithm form of the
actual completion valuation: writing log |x|_v for the logarithm
completionValuationAdd of the Mathlib value of x, the realified degree is
log |x|_v times log #(O_F / v). -/
theorem finitePlaceUnitValueKernel_realification_eq_valuationLog
    (v : HeightOneSpectrum (𝓞 F)) (x : finitePlaceUnitValueMonoid (F := F) v) :
    (finitePlaceUnitValueKernel (F := F) v).realification x =
      completionValuationAdd v x *
        Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) := by
  rw [finitePlaceUnitValueKernel_realification, completionValuationExponent_eq_neg]
  push_cast
  ring

/-- The degree kernel of the prime strip at a finite place, at the value-group
level: the FrobenioidValueKernel on the value group.  Its degree is the value
monoid degree map of the source F-prime-strip. -/
noncomputable def finitePlaceValueGroupKernel (v : HeightOneSpectrum (𝓞 F)) :
    FrobenioidValueKernel (finitePlaceValueGroup) where
  degree := finitePlaceValueGroupDegree (F := F) v
  realification := fun n =>
    -((Multiplicative.toAdd n : ℤ) : ℝ) *
      Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ))
  realification_mul := by
    intro x y
    rw [toAdd_mul]
    push_cast
    ring
  degree_realification := by
    intro x
    rfl
  unit := 1
  unit_realification := by
    simp
  effective := fun _ => True
  effective_proved := fun _ => trivial
  transport := id
  transport_degree := by
    intro x
    rfl

/-- The realification of the value-group degree kernel of a value of exponent
n is -n * log #(O_F / v). -/
@[simp]
theorem finitePlaceValueGroupKernel_realification (v : HeightOneSpectrum (𝓞 F))
    (n : finitePlaceValueGroup) :
    (finitePlaceValueGroupKernel (F := F) v).realification n =
      -((Multiplicative.toAdd n : ℤ) : ℝ) *
        Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) :=
  rfl

/-- The value-group degree is injective: the degree kernel on the value group
is trivial.  This is the prime-strip form of the fact that a nonzero exponent
has a nonzero log-volume degree. -/
theorem finitePlaceValueGroupDegree_injective (v : HeightOneSpectrum (𝓞 F)) :
    Function.Injective (finitePlaceValueGroupDegree (F := F) v) := by
  intro x y hxy
  have hout := congrArg Multiplicative.toAdd hxy
  simp only [finitePlaceValueGroupDegree_apply, toAdd_ofAdd] at hout
  have hreal : ((Multiplicative.toAdd x : ℤ) : ℝ) =
      ((Multiplicative.toAdd y : ℤ) : ℝ) := by
    have h' : ((Multiplicative.toAdd x : ℤ) : ℝ) *
        Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) =
        ((Multiplicative.toAdd y : ℤ) : ℝ) *
          Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) := by
      linarith
    exact mul_right_cancel₀ (finitePlaceResidueCardinality_log_ne_zero (F := F) v) h'
  exact Multiplicative.toAdd.injective (Int.cast_injective (α := ℝ) hreal)

/-- The degree of a value-group element is one exactly when the value is one:
the value-group degree kernel is trivial. -/
theorem finitePlaceValueGroupDegree_eq_one_iff (v : HeightOneSpectrum (𝓞 F))
    (n : finitePlaceValueGroup) :
    finitePlaceValueGroupDegree (F := F) v n = 1 ↔ n = 1 := by
  constructor
  · intro h
    apply finitePlaceValueGroupDegree_injective (F := F) v
    rw [h, map_one]
  · intro h
    rw [h, map_one]

/-- The degree kernel of the unit-level value monoid is the group of integral
units O_v^x: a completion unit has degree one exactly when its classical
exponent vanishes. -/
theorem finitePlaceUnitValueKernel_degree_eq_one_iff_mem_integralUnits
    (v : HeightOneSpectrum (𝓞 F)) (x : finitePlaceUnitValueMonoid (F := F) v) :
    finitePlaceLocalDegree (F := F) v x = 1 ↔
      x ∈ (v.adicCompletionIntegers F).units := by
  rw [finitePlaceLocalDegree_apply, ofAdd_eq_one,
    finitePlaceResidueCardinality_neg_mul_log_eq_zero_iff,
    completionValuationExponent_eq_zero_iff_mem_integralUnits]

/-! ## 4. The Example 3.6 finite-place value data through the prime strip -/

/-- The global units embedded in the units of the actual v-adic completion:
the comparison map from the global multiplicative group F^x to the local
value monoid at the finite place v. -/
noncomputable def finitePlaceGlobalUnitValue (v : HeightOneSpectrum (𝓞 F)) :
    Fˣ →* finitePlaceUnitValueMonoid (F := F) v :=
  Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom

/-- The completion exponent of an embedded global unit is the finite-place
integer exponent nu_v of the Example 3.6 data.  This is the sign-correct form
of the global/local value bridge
numberFieldGlobalPlaceData_finiteDelta_eq_completionValuationExponent. -/
theorem finitePlaceGlobalUnitValue_exponent (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    completionValuationExponent v (finitePlaceGlobalUnitValue (F := F) v f) =
      finitePlaceValueExponent v f := by
  change completionValuationExponent v
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom f) =
    finitePlaceValueExponent v f
  rw [← numberFieldGlobalPlaceData_finiteDelta_eq_completionValuationExponent (F := F) v f]
  exact numberFieldGlobalPlaceData_finiteDelta (F := F) f v

/-- The additive principal map of the finite-place LocalValueData of
Example 3.6 is the value-group coordinate of the prime strip applied to the
embedded global unit. -/
theorem numberFieldFiniteLocalValueData_deltaAdd_eq_primeStripValue
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (numberFieldFiniteLocalValueData (F := F) v).deltaAdd f =
      Multiplicative.toAdd
        (finitePlaceLocalValue (F := F) v (finitePlaceGlobalUnitValue (F := F) v f)) := by
  rw [numberFieldFiniteLocalValueData_deltaAdd, finitePlaceLocalValue_apply, toAdd_ofAdd]
  exact (finitePlaceGlobalUnitValue_exponent (F := F) v f).symm

/-- **The structure-map agreement at a finite place.**  The local principal
map delta_v : F^x -> Gamma_v of the finite-place LocalValueData of
Example 3.6 is exactly the composite of the prime-strip value-group
coordinate with the embedding of global units into the completion units. -/
theorem numberFieldFiniteLocalValueData_delta_eq_primeStripValue
    (v : HeightOneSpectrum (𝓞 F)) :
    (numberFieldFiniteLocalValueData (F := F) v).delta =
      (finitePlaceLocalValue (F := F) v).comp
        (finitePlaceGlobalUnitValue (F := F) v) := by
  ext f
  rw [MonoidHom.comp_apply]
  change Multiplicative.ofAdd
      ((numberFieldFiniteLocalValueData (F := F) v).deltaAdd f) =
    completionValuationExponentMonoidHom v (finitePlaceGlobalUnitValue (F := F) v f)
  rw [numberFieldFiniteLocalValueData_deltaAdd,
    completionValuationExponentMonoidHom_apply, finitePlaceGlobalUnitValue_exponent]

/-- The realified finite-place prime-strip degree of an embedded global unit
is the negated Example 3.6 finite exponent times the residue-field
logarithm. -/
theorem finitePlaceUnitValueKernel_realification_globalUnit
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (finitePlaceUnitValueKernel (F := F) v).realification
        (finitePlaceGlobalUnitValue (F := F) v f) =
      -((numberFieldFiniteLocalValueData (F := F) v).deltaAdd f : ℝ) *
        Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) := by
  rw [finitePlaceUnitValueKernel_realification,
    numberFieldFiniteLocalValueData_deltaAdd,
    finitePlaceGlobalUnitValue_exponent]

/-- The same realified degree, read from the packaged global place data: the
finite coordinate finiteDelta f v of GlobalPlaceData. -/
theorem finitePlaceUnitValueKernel_realification_globalPlaceData
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (finitePlaceUnitValueKernel (F := F) v).realification
        (finitePlaceGlobalUnitValue (F := F) v f) =
      -((numberFieldGlobalPlaceData (F := F)).finiteDelta f v : ℝ) *
        Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) := by
  rw [finitePlaceUnitValueKernel_realification_globalUnit,
    numberFieldFiniteLocalValueData_deltaAdd,
    numberFieldGlobalPlaceData_finiteDelta]

/-! ## 5. The archimedean value monoid and its degree kernel -/

/-- The archimedean local value monoid of the prime strip: the value group of
an archimedean place, written in multiplicative notation. -/
abbrev archimedeanValueGroup : Type := Multiplicative ℝ

/-- The local principal value at the archimedean place w, from the actual
absolute value: a global unit f is sent to the value-group element
-log (w f). -/
noncomputable def archimedeanPlaceValueUnit (w : NumberField.InfinitePlace F) :
    Fˣ →* archimedeanValueGroup :=
  archimedeanPlaceValueMonoidHom w

/-- The archimedean principal value of a global unit is -log (w f) in the
value group. -/
@[simp]
theorem archimedeanPlaceValueUnit_apply (w : NumberField.InfinitePlace F) (f : Fˣ) :
    archimedeanPlaceValueUnit (F := F) w f =
      Multiplicative.ofAdd (archimedeanPlaceValue w f) :=
  rfl

/-- The degree kernel of the prime strip at an archimedean place: the
FrobenioidValueKernel on the value group, with the identity degree map.  Its
realification is the additive form of the value, so the realification of the
principal value of a global unit is -log (w f). -/
noncomputable def archimedeanValueGroupKernel : FrobenioidValueKernel archimedeanValueGroup where
  degree := MonoidHom.id archimedeanValueGroup
  realification := fun r => Multiplicative.toAdd r
  realification_mul := by
    intro x y
    rfl
  degree_realification := by
    intro x
    rfl
  unit := 1
  unit_realification := by
    simp
  effective := fun _ => True
  effective_proved := fun _ => trivial
  transport := id
  transport_degree := by
    intro x
    rfl

/-- The realification of the archimedean value-group kernel is the additive
form of the value. -/
@[simp]
theorem archimedeanValueGroupKernel_realification (r : archimedeanValueGroup) :
    archimedeanValueGroupKernel.realification r = Multiplicative.toAdd r :=
  rfl

/-- **The archimedean realification is -log (w f).**  The realified degree of
the prime-strip value of a global unit at an archimedean place is exactly the
archimedean principal value -log (w f) of the actual absolute value. -/
theorem archimedeanValueGroupKernel_realification_globalUnit
    (w : NumberField.InfinitePlace F) (f : Fˣ) :
    archimedeanValueGroupKernel.realification (archimedeanPlaceValueUnit (F := F) w f) =
      -Real.log (w (f : F)) := by
  rw [archimedeanValueGroupKernel_realification, archimedeanPlaceValueUnit_apply,
    toAdd_ofAdd, archimedeanPlaceValue]

/-- The archimedean realification of an embedded global unit equals the
infiniteDelta of the packaged global place data: the prime-strip value and the
Example 3.6 archimedean coordinate agree on global units. -/
theorem archimedeanValueGroupKernel_realification_infiniteDelta
    (w : NumberField.InfinitePlace F) (f : Fˣ) :
    archimedeanValueGroupKernel.realification (archimedeanPlaceValueUnit (F := F) w f) =
      (numberFieldGlobalPlaceData (F := F)).infiniteDelta f w := by
  rw [archimedeanValueGroupKernel_realification_globalUnit,
    numberFieldGlobalPlaceData_infiniteDelta]

/-- The local principal map of the archimedean LocalValueData of Example 3.6
is exactly the prime-strip archimedean value map. -/
theorem numberFieldInfiniteLocalValueData_delta_eq_archimedeanPlaceValueUnit
    (w : NumberField.InfinitePlace F) :
    (numberFieldInfiniteLocalValueData (F := F) w).delta =
      archimedeanPlaceValueUnit (F := F) w :=
  rfl

/-- The realification of the archimedean value-group kernel is surjective onto
the real line: the archimedean value group is all of the reals. -/
theorem archimedeanValueGroupKernel_realification_surjective :
    Function.Surjective archimedeanValueGroupKernel.realification := by
  intro r
  exact ⟨Multiplicative.ofAdd r, toAdd_ofAdd r⟩

/-- The degree of the archimedean value-group kernel is one exactly for the
unit value. -/
theorem archimedeanValueGroupKernel_degree_eq_one_iff
    (r : archimedeanValueGroup) :
    archimedeanValueGroupKernel.degree r = 1 ↔ r = 1 :=
  Iff.rfl

/-! ## 6. Frobenius power compatibility with the Example 3.6 exponents -/

/-- The value side of item (4) of the frozen boundary: the realified degree of
an n-th Frobenius power of a completion unit is n times the realified degree
of the unit. -/
theorem finitePlaceUnitValueKernel_realification_pow
    (v : HeightOneSpectrum (𝓞 F)) (x : finitePlaceUnitValueMonoid (F := F) v) (n : ℕ) :
    (finitePlaceUnitValueKernel (F := F) v).realification (x ^ n) =
      (n : ℝ) * (finitePlaceUnitValueKernel (F := F) v).realification x :=
  valueFrobeniusPower_realification (finitePlaceUnitValueKernel (F := F) v) x n

/-- The value-group degree of the n-th Frobenius power is the n-th power of
the degree, via valueFrobeniusPower of the prime-strip skeleton. -/
theorem finitePlaceValueGroupDegree_valueFrobeniusPower
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ+) (x : finitePlaceValueGroup) :
    finitePlaceValueGroupDegree (F := F) v (valueFrobeniusPower n x) =
      (finitePlaceValueGroupDegree (F := F) v x) ^ (n : ℕ) :=
  valueFrobeniusPower_degree (finitePlaceValueGroupKernel (F := F) v) n x

/-- The value-group realification of the n-th Frobenius power is n times the
realification of the value. -/
theorem finitePlaceValueGroupKernel_realification_pow
    (v : HeightOneSpectrum (𝓞 F)) (x : finitePlaceValueGroup) (n : ℕ) :
    (finitePlaceValueGroupKernel (F := F) v).realification (x ^ n) =
      (n : ℝ) * (finitePlaceValueGroupKernel (F := F) v).realification x :=
  valueFrobeniusPower_realification (finitePlaceValueGroupKernel (F := F) v) x n

/-- **Frobenius compatibility at a finite place.**  The realified
finite-place prime-strip degree of the n-th Frobenius power of the embedded
global unit f is n times the realified degree of f, matching
GlobalPlaceData.finiteDelta_pow. -/
theorem finitePlaceUnitValueKernel_realification_frobenius_globalUnit
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) (n : ℕ) :
    (finitePlaceUnitValueKernel (F := F) v).realification
        ((finitePlaceGlobalUnitValue (F := F) v f) ^ n) =
      (n : ℝ) *
        (finitePlaceUnitValueKernel (F := F) v).realification
          (finitePlaceGlobalUnitValue (F := F) v f) :=
  valueFrobeniusPower_realification (finitePlaceUnitValueKernel (F := F) v)
    (finitePlaceGlobalUnitValue (F := F) v f) n

/-- The finite-place Example 3.6 exponent of the n-th power, read through the
prime-strip realification: it is n times the exponent of f. -/
theorem numberFieldFiniteDelta_pow_realification
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) (n : ℕ) :
    -((numberFieldGlobalPlaceData (F := F)).finiteDelta (f ^ n) v : ℝ) *
        Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) =
      (n : ℝ) *
        (-((numberFieldGlobalPlaceData (F := F)).finiteDelta f v : ℝ) *
          Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ))) := by
  rw [GlobalPlaceData.finiteDelta_pow, nsmul_eq_mul]
  push_cast
  ring

/-- The archimedean realification of the n-th Frobenius power of a value is n
times the realification of the value. -/
theorem archimedeanValueGroupKernel_realification_pow
    (r : archimedeanValueGroup) (n : ℕ) :
    archimedeanValueGroupKernel.realification (r ^ n) =
      (n : ℝ) * archimedeanValueGroupKernel.realification r :=
  valueFrobeniusPower_realification archimedeanValueGroupKernel r n

/-- The archimedean principal value of the n-th power of a global unit is n
times the principal value: -log (w (f^n)) = n * (-log (w f)), matching
GlobalPlaceData.infiniteDelta_pow. -/
theorem archimedeanPlaceValue_pow (w : NumberField.InfinitePlace F) (f : Fˣ) (n : ℕ) :
    -Real.log (w ((f ^ n : Fˣ) : F)) = (n : ℝ) * (-Real.log (w (f : F))) := by
  have h := GlobalPlaceData.infiniteDelta_pow (numberFieldGlobalPlaceData (F := F)) f n w
  rw [numberFieldGlobalPlaceData_infiniteDelta,
    numberFieldGlobalPlaceData_infiniteDelta] at h
  rw [h, nsmul_eq_mul]

/-! ## 7. Docking with the model-Frobenioid input of the backend -/

namespace SourceModelBackendDocking

open SourceModelBackend

/-- The rational-function carrier of the model-Frobenioid input at its bottom
object is the additive group of global units, i.e. the domain of the
prime-strip value maps. -/
theorem sourceModelInput_rationalFunctions_carrier :
    (numberFieldSourceModelInput (F := F)).rationalFunctions.obj
        SourceModelBackend.bottomPoint = Additive Fˣ :=
  rfl

/-- The divisor map of the model-Frobenioid input at the bottom object is the
explicit principal divisor map. -/
theorem sourceModelInput_divisor_eq_globalModelDivisor (u : Additive Fˣ) :
    (numberFieldSourceModelInput (F := F)).divisor SourceModelBackend.bottomPoint u =
      globalModelDivisor (F := F) u :=
  rfl

/-- The group completion comparison of the model divisor recovers the explicit
principal divisor of a rational function. -/
theorem globalModelDivisor_coneComparison (u : Additive Fˣ) :
    coneGrothendieckEquiv (F := F) (globalModelDivisor (F := F) u) =
      principalDivisorExplicit (F := F) u := by
  simp [globalModelDivisor]

/-- The finite coordinate of the explicit principal divisor is the finite-place
integer exponent of the rational function. -/
theorem principalDivisorExplicit_fst (u : Additive Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (principalDivisorExplicit (F := F) u).1 v = finitePlaceValueExponent v u.toMul :=
  rfl

/-- The finite coordinate of the explicit principal divisor is the completion
exponent of the embedded global unit, i.e. the prime-strip finite-place value. -/
theorem principalDivisorExplicit_fst_eq_completionExponent
    (u : Additive Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (principalDivisorExplicit (F := F) u).1 v =
      completionValuationExponent v (finitePlaceGlobalUnitValue (F := F) v u.toMul) := by
  rw [principalDivisorExplicit_fst, finitePlaceGlobalUnitValue_exponent]

/-- The archimedean coordinate of the explicit principal divisor is the
archimedean principal value of the rational function. -/
theorem principalDivisorExplicit_snd (u : Additive Fˣ) (w : NumberField.InfinitePlace F) :
    (principalDivisorExplicit (F := F) u).2 w = archimedeanPlaceValue w u.toMul :=
  rfl

/-- The finite coordinate of the backend divisor map is the completion
exponent of the embedded global unit. -/
theorem sourceModelInput_divisor_fst_eq_completionExponent
    (u : Additive Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (coneGrothendieckEquiv (F := F)
        ((numberFieldSourceModelInput (F := F)).divisor
          SourceModelBackend.bottomPoint u)).1 v =
      completionValuationExponent v (finitePlaceGlobalUnitValue (F := F) v u.toMul) := by
  rw [sourceModelInput_divisor_eq_globalModelDivisor, globalModelDivisor_coneComparison,
    principalDivisorExplicit_fst_eq_completionExponent]

/-- The finite coordinate of the backend divisor map is the finite-place
integer exponent of the rational function, in the form used by the Ex3.6
finite local value data. -/
theorem sourceModelInput_divisor_fst_eq_finiteExponent
    (u : Additive Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (coneGrothendieckEquiv (F := F)
        ((numberFieldSourceModelInput (F := F)).divisor
          SourceModelBackend.bottomPoint u)).1 v =
      finitePlaceValueExponent v u.toMul := by
  rw [sourceModelInput_divisor_fst_eq_completionExponent,
    finitePlaceGlobalUnitValue_exponent]

/-- The archimedean coordinate of the backend divisor map is the prime-strip
archimedean value: -log (w u), the realification of the archimedean
value-group element of the rational function. -/
theorem sourceModelInput_divisor_snd_eq_archimedeanValue
    (u : Additive Fˣ) (w : NumberField.InfinitePlace F) :
    (coneGrothendieckEquiv (F := F)
        ((numberFieldSourceModelInput (F := F)).divisor
          SourceModelBackend.bottomPoint u)).2 w =
      archimedeanValueGroupKernel.realification
        (archimedeanPlaceValueUnit (F := F) w u.toMul) := by
  rw [sourceModelInput_divisor_eq_globalModelDivisor, globalModelDivisor_coneComparison,
    principalDivisorExplicit_snd]
  exact (archimedeanValueGroupKernel_realification_globalUnit (F := F) w u.toMul).symm

/-- The realified finite-place prime-strip degree of a rational function in
the backend coordinates is the negated backend finite coordinate times the
residue-field logarithm. -/
theorem sourceModelInput_divisor_fst_realification
    (u : Additive Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (finitePlaceUnitValueKernel (F := F) v).realification
        (finitePlaceGlobalUnitValue (F := F) v u.toMul) =
      -((coneGrothendieckEquiv (F := F)
          ((numberFieldSourceModelInput (F := F)).divisor
            SourceModelBackend.bottomPoint u)).1 v : ℝ) *
        Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) := by
  rw [finitePlaceUnitValueKernel_realification_globalUnit,
    numberFieldFiniteLocalValueData_deltaAdd]
  rw [← sourceModelInput_divisor_fst_eq_finiteExponent]

end SourceModelBackendDocking

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
