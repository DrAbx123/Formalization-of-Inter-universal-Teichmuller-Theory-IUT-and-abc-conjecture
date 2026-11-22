import LeanFormal.IUT.IUTII.Frobenioid.Example36QuadraticRamification
import LeanFormal.IUT.IUTII.Frobenioid.Example36TorsorTransport
import LeanFormal.IUT.IUTII.Frobenioid.Example36TorsorEquivalence
import LeanFormal.IUT.IUTII.Frobenioid.Example36GlobalIdealFamilyActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36NumberFieldPlaceCompletionBridge
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFullPrimePacket
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Tactic

/-!
# Concrete ramified transport example: Q(sqrt 2) / Q above the prime 2

This module instantiates the abstract place-localization transport of
Example36FrobenioidTransport at the concrete quadratic number field
Q(sqrt 2) of Example36QuadraticRamification, and transports concrete ideal
families and torsor presentations along it.

## Contents

1. The concrete transport datum quadraticSquareRootTwoTransport of
   Example36TransportInstance (finite places by ideal contraction, genuine
   ramification indices ramificationIndexAtUpperPlace, archimedean places by
   restriction of absolute values), restated at the concrete field.
2. The concrete rational finite place (2) of Q, constructed from the
   canonical equivalence between the finite places of Q and the prime
   numbers, and a concrete upper place of Q(sqrt 2) above it.  The chosen
   upper place has the actual arithmetic ramification index
   ramificationIndexAtUpperPlace; the numerical value e = 2 is not proved
   here (see the boundary).
3. The concrete global unit 2 of Q: its value at the rational place (2) is
   provably nonzero, so the transported finite coordinate of the
   principal-divisor shift is nonzero.  This is the ramified/non-trivial
   behaviour statement (no identity transport is substituted at the place
   above 2).
4. The transported finite-coordinate/Delta laws at the concrete places, with
   the actual ramification-index symbol; the transport of the concrete ideal
   family div(2) and of its torsor presentation; the transported principal
   translation arrow; and the completion-valuation identities of the
   instance.

## Boundary (what is coordinate/arithmetic-level and what is missing)

* The ramification index is the actual ramificationIndexAtUpperPlace of the
  instance, never an assumed constant.  The numerical computation e = 2 at
  the place above (2) is still open: it is
  quadraticRamificationMissingComputation of Example36TransportInstance /
  quadraticSqrtTwoRamificationMissing of Example36QuadraticRamification (the
  prime-ideal input quadraticSqrtTwoPrimeMissing is the missing ingredient
  for that computation).
* Consequently the HeightOneSpectrum HeightOneSpectrum.mk (span {sqrtTwoInteger})
  for the place Q = (sqrt 2) itself cannot be constructed in this file: its
  primality is exactly quadraticSqrtTwoPrimeMissing.  Instead we use the
  concrete rational place (2) and a concrete upper place above it, for which
  the transport laws hold with the actual ramification-index symbol.
* The lower value nu_(2)(2) is proved nonzero but its exact value is not
  computed here; every transported coordinate is stated as
  e(w) * nu_(2)(2) with the actual symbol e(w).
* No theta-pilot, q-pilot or Tate claim is made.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open scoped NumberField WithZero
open IsDedekindDomain NumberField
open LeanFormal.IUT.NumberFieldFinitePlace

/-- The instance that the rational prime 2 is prime. -/
instance quadraticExampleFactPrimeTwo : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The concrete quadratic field of the example: Q(sqrt 2). -/
abbrev quadraticExampleField : Type := quadraticSqrtTwoField

/-- The global unit 2 of Q. -/
def quadraticExampleTwoUnit : ℚˣ :=
  Units.mk0 (2 : ℚ) (by norm_num)

@[simp]
theorem quadraticExampleTwoUnit_val : ((quadraticExampleTwoUnit : ℚˣ) : ℚ) = 2 :=
  rfl

/-- The concrete rational finite place (2) of Q, as the maximal ideal of the
canonical rational finite place at the prime 2. -/
noncomputable def quadraticRationalTwoPlace : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm
    ⟨2, Fact.out⟩

/-- The rational prime underneath quadraticRationalTwoPlace is 2. -/
theorem quadraticRationalTwoPlace_primesEquiv_val :
    ((Rat.HeightOneSpectrum.primesEquiv
        (quadraticRationalTwoPlace : HeightOneSpectrum (𝓞 ℚ)) : Nat.Primes) : ℕ) = 2 := by
  simp [quadraticRationalTwoPlace]

/-- The maximal ideal of the canonical rational finite place at 2 is the
concrete height-one spectrum quadraticRationalTwoPlace. -/
theorem rationalFinitePlace_maximalIdeal_two :
    (rationalFinitePlace 2).maximalIdeal = quadraticRationalTwoPlace := by
  unfold rationalFinitePlace quadraticRationalTwoPlace
  rw [NumberField.FinitePlace.maximalIdeal_mk]

/-- The value of the global unit 2 at the concrete rational place (2) is
nonzero.  This is the concrete non-vanishing input for the ramified example. -/
theorem quadraticRationalTwoPlace_two_value_ne_zero :
    finitePlaceValueExponent (quadraticRationalTwoPlace : HeightOneSpectrum (𝓞 ℚ))
      quadraticExampleTwoUnit ≠ 0 := by
  intro hzero
  have hlog : WithZero.log
      ((quadraticRationalTwoPlace : HeightOneSpectrum (𝓞 ℚ)).valuation ℚ
        (quadraticExampleTwoUnit : ℚ)) = 0 := by
    have h := hzero
    unfold finitePlaceValueExponent at h
    simpa using neg_eq_zero.mp h
  have hne : (quadraticRationalTwoPlace : HeightOneSpectrum (𝓞 ℚ)).valuation ℚ
      (quadraticExampleTwoUnit : ℚ) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    rw [quadraticExampleTwoUnit_val]
    norm_num
  have hval : (quadraticRationalTwoPlace : HeightOneSpectrum (𝓞 ℚ)).valuation ℚ
      (quadraticExampleTwoUnit : ℚ) = 1 := by
    calc (quadraticRationalTwoPlace : HeightOneSpectrum (𝓞 ℚ)).valuation ℚ
          (quadraticExampleTwoUnit : ℚ)
        = WithZero.exp (WithZero.log
            ((quadraticRationalTwoPlace : HeightOneSpectrum (𝓞 ℚ)).valuation ℚ
              (quadraticExampleTwoUnit : ℚ))) := (WithZero.exp_log hne).symm
      _ = WithZero.exp 0 := by rw [hlog]
      _ = 1 := by simp
  have hlt : (quadraticRationalTwoPlace : HeightOneSpectrum (𝓞 ℚ)).valuation ℚ
      (quadraticExampleTwoUnit : ℚ) < 1 := by
    have he : ((quadraticRationalTwoPlace : HeightOneSpectrum (𝓞 ℚ)).valuation ℚ).IsEquiv
        (Rat.padicValuation 2) := by
      simpa only [quadraticRationalTwoPlace_primesEquiv_val] using
        Rat.HeightOneSpectrum.valuation_equiv_padicValuation
          (quadraticRationalTwoPlace : HeightOneSpectrum (𝓞 ℚ))
    have hpad : Rat.padicValuation 2 (2 : ℚ) < 1 := by
      have hpad_eq : Rat.padicValuation 2 (2 : ℚ) = WithZero.exp (-1) := by
        simpa using Rat.padicValuation_self 2
      rw [hpad_eq]
      rw [show (1 : ℤᵐ⁰) = WithZero.exp 0 from WithZero.exp_zero.symm]
      exact WithZero.exp_lt_exp.mpr (by norm_num)
    have hpad' : Rat.padicValuation 2 (quadraticExampleTwoUnit : ℚ) < 1 := by
      simpa [quadraticExampleTwoUnit_val] using hpad
    exact (Valuation.isEquiv_iff_val_lt_one.mp he).mpr hpad'
  exact absurd hval (ne_of_lt hlt)


/-! ## The concrete upper place above (2) -/

/-- A concrete finite place of Q(sqrt 2) above the rational place (2).  This is
chosen from the (proved nonempty) finite set of places above (2); its actual
ramification index is the genuine arithmetic ramification index. -/
noncomputable def quadraticUpperPlaceAboveTwo :
    FinitePlaceAtPrime quadraticExampleField 2 :=
  Classical.choice (nonempty_fullPrimePlaces (K := quadraticExampleField) (p := 2))

/-- The underlying height-one spectrum of the concrete upper place. -/
noncomputable def quadraticUpperPlace :
    HeightOneSpectrum (𝓞 quadraticExampleField) :=
  quadraticUpperPlaceAboveTwo.val.maximalIdeal

/-- The concrete upper place lies above the concrete rational place (2). -/
theorem quadraticUpperPlace_restriction :
    upperPlaceRestriction (F := ℚ) quadraticUpperPlace =
      (quadraticRationalTwoPlace : HeightOneSpectrum (𝓞 ℚ)) := by
  unfold quadraticUpperPlace upperPlaceRestriction
  rw [NumberField.FinitePlace.mk_maximalIdeal]
  rw [comap_eq_rationalFinitePlace quadraticUpperPlaceAboveTwo]
  exact rationalFinitePlace_maximalIdeal_two

/-- The concrete transport datum is exactly the generic number-field-extension
instance at Q(sqrt 2)/Q of Example36TransportInstance. -/
theorem quadraticSquareRootTwoTransport_spec :
    (quadraticSquareRootTwoTransport :
      PlaceLocalizationTransport (numberFieldGlobalPlaceData (F := ℚ))
        (numberFieldGlobalPlaceData (F := quadraticExampleField))) =
      PlaceLocalizationTransport.ofNumberFieldExtension (F := ℚ)
        (F' := quadraticExampleField) :=
  rfl

/-- The finite-place restriction of the concrete quadratic transport is the
upper-place restriction. -/
@[simp]
theorem quadraticSquareRootTwoTransport_finitePlaceRestriction
    (w : HeightOneSpectrum (𝓞 quadraticExampleField)) :
    quadraticSquareRootTwoTransport.finitePlaceRestriction w =
      upperPlaceRestriction (F := ℚ) w :=
  rfl

/-- The field map of the concrete quadratic transport is the structural map
from Q to Q(sqrt 2). -/
@[simp]
theorem quadraticSquareRootTwoTransport_fieldMap :
    quadraticSquareRootTwoTransport.fieldMap =
      (algebraMap ℚ quadraticExampleField : ℚ →+* quadraticExampleField) :=
  rfl

/-- **The concrete finite-place Delta transport law**, stated with the actual
arithmetic ramification index ramificationIndexAtUpperPlace (not a hypothesis). -/
theorem quadraticSquareRootTwoTransport_finiteDelta (f : ℚˣ)
    (w : HeightOneSpectrum (𝓞 quadraticExampleField)) :
    (numberFieldGlobalPlaceData (F := quadraticExampleField)).finiteDelta
        (unitsMapOfRingHom (algebraMap ℚ quadraticExampleField) f) w =
      (ramificationIndexAtUpperPlace (F := ℚ) (F' := quadraticExampleField) w : ℤ) *
        (numberFieldGlobalPlaceData (F := ℚ)).finiteDelta f
          (upperPlaceRestriction (F := ℚ) w) :=
  quadraticSquareRootTwoTransport.finiteDelta_transport f w

/-- The concrete Delta law for the global unit 2 at the concrete upper place,
with the actual ramification index and the concrete lower coordinate. -/
theorem quadraticSquareRootTwoTransport_two_finiteDelta :
    (numberFieldGlobalPlaceData (F := quadraticExampleField)).finiteDelta
        (unitsMapOfRingHom (algebraMap ℚ quadraticExampleField) quadraticExampleTwoUnit)
        quadraticUpperPlace =
      (ramificationIndexAtUpperPlace (F := ℚ) (F' := quadraticExampleField)
          quadraticUpperPlace : ℤ) *
        finitePlaceValueExponent
          (quadraticRationalTwoPlace : HeightOneSpectrum (𝓞 ℚ))
          quadraticExampleTwoUnit := by
  have h := quadraticSquareRootTwoTransport_finiteDelta quadraticExampleTwoUnit
    quadraticUpperPlace
  rw [quadraticUpperPlace_restriction, numberFieldGlobalPlaceData_finiteDelta] at h
  exact h

/-- The transported finite coordinate of the global unit 2 at the concrete
upper place is nonzero: the concrete ramified behaviour statement. -/
theorem quadraticSquareRootTwoTransport_two_finiteDelta_ne_zero :
    (numberFieldGlobalPlaceData (F := quadraticExampleField)).finiteDelta
        (unitsMapOfRingHom (algebraMap ℚ quadraticExampleField) quadraticExampleTwoUnit)
        quadraticUpperPlace ≠ 0 := by
  rw [quadraticSquareRootTwoTransport_two_finiteDelta]
  have he : ((ramificationIndexAtUpperPlace (F := ℚ) (F' := quadraticExampleField)
      quadraticUpperPlace : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (ramificationIndexAtUpperPlace_pos (F := ℚ)
      (F' := quadraticExampleField) quadraticUpperPlace).ne'
  exact mul_ne_zero he quadraticRationalTwoPlace_two_value_ne_zero

/-! ## Transport of the concrete ideal family and presentation -/

/-- The concrete ideal family of the example: the principal divisor of the
global unit 2. -/
noncomputable def quadraticExampleIdealFamily : GlobalIdealFamily ℚ :=
  principalDivisor quadraticExampleTwoUnit

/-- The finite coordinate of the concrete ideal family at the rational place (2). -/
theorem quadraticExampleIdealFamily_finite :
    quadraticExampleIdealFamily.finite
        (quadraticRationalTwoPlace : HeightOneSpectrum (𝓞 ℚ)) =
      finitePlaceValueExponent
        (quadraticRationalTwoPlace : HeightOneSpectrum (𝓞 ℚ))
        quadraticExampleTwoUnit := by
  change principalDivisorFinite quadraticExampleTwoUnit
      (quadraticRationalTwoPlace : HeightOneSpectrum (𝓞 ℚ)) = _
  exact principalDivisorFinite_apply quadraticExampleTwoUnit
    (quadraticRationalTwoPlace : HeightOneSpectrum (𝓞 ℚ))

/-- **Transported ideal-family coordinate law** at the concrete upper place:
the transported finite coordinate is the ramification multiple of the source
coordinate. -/
theorem quadraticTransportedIdealFamily_finite :
    (quadraticSquareRootTwoTransport.transportObject
        quadraticExampleIdealFamily).finite quadraticUpperPlace =
      (ramificationIndexAtUpperPlace (F := ℚ) (F' := quadraticExampleField)
          quadraticUpperPlace : ℤ) *
        finitePlaceValueExponent
          (quadraticRationalTwoPlace : HeightOneSpectrum (𝓞 ℚ))
          quadraticExampleTwoUnit := by
  rw [PlaceLocalizationTransport.transportObject_finite_apply]
  rw [quadraticSquareRootTwoTransport_ramificationIndex]
  rw [quadraticSquareRootTwoTransport_finitePlaceRestriction]
  rw [quadraticUpperPlace_restriction]
  rw [quadraticExampleIdealFamily_finite]

/-- The transported concrete ideal family has nonzero finite coordinate at the
concrete upper place. -/
theorem quadraticTransportedIdealFamily_finite_ne_zero :
    (quadraticSquareRootTwoTransport.transportObject
        quadraticExampleIdealFamily).finite quadraticUpperPlace ≠ 0 := by
  rw [quadraticTransportedIdealFamily_finite]
  have he : ((ramificationIndexAtUpperPlace (F := ℚ) (F' := quadraticExampleField)
      quadraticUpperPlace : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (ramificationIndexAtUpperPlace_pos (F := ℚ)
      (F' := quadraticExampleField) quadraticUpperPlace).ne'
  exact mul_ne_zero he quadraticRationalTwoPlace_two_value_ne_zero

/-- The torsor presentation of the concrete ideal family. -/
noncomputable def quadraticExamplePresentation :
    TorsorPresentation (numberFieldGlobalPlaceData (F := ℚ)) :=
  idealFamilyToPresentation (numberFieldGlobalPlaceData (F := ℚ))
    quadraticExampleIdealFamily

/-- The transported torsor presentation. -/
noncomputable def quadraticTransportedPresentation :
    TorsorPresentation (numberFieldGlobalPlaceData (F := quadraticExampleField)) :=
  quadraticSquareRootTwoTransport.transportTorsorPresentation
    quadraticExamplePresentation

/-- **Transported presentation coordinate law** at the concrete upper place. -/
theorem quadraticTransportedPresentation_finiteCoord :
    quadraticTransportedPresentation.finiteCoord quadraticUpperPlace =
      (ramificationIndexAtUpperPlace (F := ℚ) (F' := quadraticExampleField)
          quadraticUpperPlace : ℤ) *
        finitePlaceValueExponent
          (quadraticRationalTwoPlace : HeightOneSpectrum (𝓞 ℚ))
          quadraticExampleTwoUnit := by
  unfold quadraticTransportedPresentation
  rw [PlaceLocalizationTransport.transportTorsorPresentation_finiteCoord]
  rw [quadraticSquareRootTwoTransport_ramificationIndex]
  rw [quadraticSquareRootTwoTransport_finitePlaceRestriction]
  rw [quadraticUpperPlace_restriction]
  rw [show quadraticExamplePresentation.finiteCoord
        (quadraticRationalTwoPlace : HeightOneSpectrum (𝓞 ℚ)) =
      quadraticExampleIdealFamily.finite
        (quadraticRationalTwoPlace : HeightOneSpectrum (𝓞 ℚ)) from
    idealFamilyToPresentation_finiteCoord
      (numberFieldGlobalPlaceData (F := ℚ)) quadraticExampleIdealFamily
      (quadraticRationalTwoPlace : HeightOneSpectrum (𝓞 ℚ))]
  rw [quadraticExampleIdealFamily_finite]

/-- The transported concrete presentation has nonzero finite coordinate at the
concrete upper place. -/
theorem quadraticTransportedPresentation_finiteCoord_ne_zero :
    quadraticTransportedPresentation.finiteCoord quadraticUpperPlace ≠ 0 := by
  rw [quadraticTransportedPresentation_finiteCoord]
  have he : ((ramificationIndexAtUpperPlace (F := ℚ) (F' := quadraticExampleField)
      quadraticUpperPlace : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (ramificationIndexAtUpperPlace_pos (F := ℚ)
      (F' := quadraticExampleField) quadraticUpperPlace).ne'
  exact mul_ne_zero he quadraticRationalTwoPlace_two_value_ne_zero

/-! ## The transported principal translation arrow -/

/-- The concrete principal translation arrow from the standard ideal family to
the principal-divisor family of 2. -/
noncomputable def quadraticExamplePrincipalArrow :
    GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := ℚ))
      (0 : GlobalIdealFamily ℚ) (0 + quadraticExampleIdealFamily) :=
  principalArrow (0 : GlobalIdealFamily ℚ) quadraticExampleTwoUnit

/-- The transported principal translation arrow is an isomorphism. -/
theorem quadraticTransportedPrincipalArrow_isIso :
    (quadraticSquareRootTwoTransport.transportHom
        quadraticExamplePrincipalArrow).IsIso :=
  PlaceLocalizationTransport.transportHom_isIso _
    (principalArrow_isIso (0 : GlobalIdealFamily ℚ) quadraticExampleTwoUnit)

/-- The transported principal translation arrow has degree one. -/
theorem quadraticTransportedPrincipalArrow_degree :
    (quadraticSquareRootTwoTransport.transportHom
        quadraticExamplePrincipalArrow).degree = 1 :=
  rfl

/-- The transported principal translation arrow has the image multiplier. -/
theorem quadraticTransportedPrincipalArrow_multiplier :
    (quadraticSquareRootTwoTransport.transportHom
        quadraticExamplePrincipalArrow).multiplier =
      unitsMapOfRingHom (algebraMap ℚ quadraticExampleField)
        quadraticExampleTwoUnit :=
  rfl

/-! ## Completion-valuation compatibility -/

/-- **Completion valuation exponent of the transported unit**: at the concrete
upper place the completion valuation exponent of the image of 2 is the
ramification multiple of the concrete lower coordinate. -/
theorem quadraticCompletionValuationExponent_two :
    completionValuationExponent quadraticUpperPlace
        (Units.map (algebraMap quadraticExampleField
          (quadraticUpperPlace.adicCompletion quadraticExampleField)).toMonoidHom
          (unitsMapOfRingHom (algebraMap ℚ quadraticExampleField)
            quadraticExampleTwoUnit)) =
      (ramificationIndexAtUpperPlace (F := ℚ) (F' := quadraticExampleField)
          quadraticUpperPlace : ℤ) *
        finitePlaceValueExponent
          (quadraticRationalTwoPlace : HeightOneSpectrum (𝓞 ℚ))
          quadraticExampleTwoUnit := by
  rw [← quadraticSquareRootTwoTransport_fieldMap]
  rw [numberFieldTransport_finiteDelta_eq_completionValuationExponent
    quadraticSquareRootTwoTransport quadraticExampleTwoUnit quadraticUpperPlace]
  rw [quadraticSquareRootTwoTransport_ramificationIndex]
  rw [quadraticSquareRootTwoTransport_finitePlaceRestriction]
  rw [quadraticUpperPlace_restriction]
  rw [numberFieldGlobalPlaceData_finiteDelta]

/-- **The instance completion-valuation identity** at the concrete upper place:
the ramification power of the lower completion valuation is the upper
completion valuation of the image. -/
theorem quadraticCompletion_valuation_pow
    (x : (upperPlaceRestriction (F := ℚ) quadraticUpperPlace).adicCompletion ℚ) :
    Valued.v x ^ (ramificationIndexAtUpperPlace (F := ℚ)
        (F' := quadraticExampleField) quadraticUpperPlace) =
      Valued.v (NumberFieldFinitePlace.completionMap (k := ℚ)
        (place := NumberField.FinitePlace.mk quadraticUpperPlace) x) :=
  NumberFieldFinitePlace.valuation_completionMap (k := ℚ)
    (place := NumberField.FinitePlace.mk quadraticUpperPlace) x

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
