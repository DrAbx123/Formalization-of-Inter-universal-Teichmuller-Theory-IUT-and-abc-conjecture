import LeanFormal.IUT.IUTII.Frobenioid.Example36QuadraticRamificationProof
import LeanFormal.IUT.IUTII.Frobenioid.Example36QuadraticTransportExample
import Mathlib.Tactic

/-!
# Strict concrete transport for Q(sqrt 2) / Q at the place (sqrt 2)

This module upgrades the fallback example of Example36QuadraticTransportExample
with the arithmetic inputs now proved in Example36QuadraticRamificationProof:

* the exact upper place sqrtTwoUpperPlace = HeightOneSpectrum.mk (span {sqrtTwoInteger})
  is constructible (primality of (sqrt 2) is proved);
* its genuine ramification index over (2) is two, as a theorem;
* the concrete lower value nu_(2)(2) is one, because 2 is a uniformizer at (2);
* hence the transported finite coordinates of the concrete ideal family and of
  the concrete torsor presentation at the exact place above (2) are exactly 2;
* the completion identity Valued.v x^2 = Valued.v (completionMap x) holds at the
  exact place.

All statements are proved; no place or ramification value is assumed.  The only
inputs are the proved arithmetic of Example36QuadraticRamificationProof and the
transport infrastructure of the integrated files.

## Boundary (not claimed)

* No general ramification formula, no statement about the other places of
  Q(sqrt 2), no completion/local-field computation beyond the displayed
  identity at the single place above (2), no global Frobenioid identification
  and no theta/q-pilot/Tate claim.
* The transport itself is the existing quadraticSquareRootTwoTransport; this
  file only evaluates and transports at the exact place above (2).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open scoped NumberField WithZero
open IsDedekindDomain NumberField
open LeanFormal.IUT.NumberFieldFinitePlace

/-- The rational place (2) as the restriction of the exact upper place (sqrt 2). -/
noncomputable def sqrtTwoRationalPlace : HeightOneSpectrum (𝓞 ℚ) :=
  upperPlaceRestriction (F := ℚ) sqrtTwoUpperPlace

/-- The exact upper place lies above the rational place (2). -/
theorem sqrtTwoUpperPlace_restriction :
    upperPlaceRestriction (F := ℚ) sqrtTwoUpperPlace = sqrtTwoRationalPlace :=
  rfl

/-- The ideal of the restricted rational place is (2). -/
theorem sqrtTwoRationalPlace_asIdeal :
    sqrtTwoRationalPlace.asIdeal = Ideal.span {(2 : 𝓞 ℚ)} := by
  unfold sqrtTwoRationalPlace upperPlaceRestriction
  rw [LeanFormal.IUT.NumberFieldFinitePlace.comap_maximalIdeal]
  rw [NumberField.FinitePlace.maximalIdeal_mk]
  unfold sqrtTwoUpperPlace
  change sqrtTwoPrincipalIdeal.under (𝓞 ℚ) = Ideal.span {(2 : 𝓞 ℚ)}
  exact sqrtTwoPrincipalIdealUnderEqSpanTwo

/-- The rational integer two is nonzero in the ring of integers of Q. -/
theorem two_ne_zero_ringOfIntegers : (2 : 𝓞 ℚ) ≠ 0 := by
  intro h
  have hmap : (2 : ℚ) = 0 := by
    simpa using congrArg (algebraMap (𝓞 ℚ) ℚ) h
  norm_num at hmap

/-- **The concrete uniformizer computation**: the integer two has valuation
exp(-1) at the rational place (2). -/
theorem sqrtTwoRationalPlace_intValuation_two :
    sqrtTwoRationalPlace.intValuation (2 : 𝓞 ℚ) = WithZero.exp (-1) := by
  have hne : (2 : 𝓞 ℚ) ≠ 0 := two_ne_zero_ringOfIntegers
  set K : ℕ :=
    (Associates.mk sqrtTwoRationalPlace.asIdeal).count
      (Associates.mk (Ideal.span {(2 : 𝓞 ℚ)})).factors with hK
  have hval : sqrtTwoRationalPlace.intValuation (2 : 𝓞 ℚ) =
      WithZero.exp (-(K : ℤ)) := by
    rw [hK]
    exact sqrtTwoRationalPlace.intValuation_if_neg hne
  have hdiv1 : sqrtTwoRationalPlace.asIdeal ∣ Ideal.span {(2 : 𝓞 ℚ)} := by
    rw [sqrtTwoRationalPlace_asIdeal]
  have hle : sqrtTwoRationalPlace.intValuation (2 : 𝓞 ℚ) ≤
      WithZero.exp (-1) := by
    simpa using (sqrtTwoRationalPlace.intValuation_le_pow_iff_dvd
      (2 : 𝓞 ℚ) 1).mpr (by rw [pow_one]; exact hdiv1)
  have hdiv2 : ¬ sqrtTwoRationalPlace.asIdeal ^ 2 ∣
      Ideal.span {(2 : 𝓞 ℚ)} := by
    rw [sqrtTwoRationalPlace_asIdeal]
    intro hdvd
    have hle2 : Ideal.span {(2 : 𝓞 ℚ)} ≤ (Ideal.span {(2 : 𝓞 ℚ)}) ^ 2 :=
      Ideal.dvd_iff_le.mp hdvd
    have hmem : (2 : 𝓞 ℚ) ∈ (Ideal.span {(2 : 𝓞 ℚ)}) ^ 2 :=
      hle2 (Ideal.mem_span_singleton_self (2 : 𝓞 ℚ))
    rw [pow_two, Ideal.span_singleton_mul_span_singleton] at hmem
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨x, hx⟩ := hmem
    have hx' := congrArg rationalIntegersHom hx
    simp only [map_mul, rationalIntegersHom_two] at hx'
    omega
  have hnle : ¬ sqrtTwoRationalPlace.intValuation (2 : 𝓞 ℚ) ≤
      WithZero.exp (-2) := by
    intro hle2
    exact hdiv2 ((sqrtTwoRationalPlace.intValuation_le_pow_iff_dvd
      (2 : 𝓞 ℚ) 2).mp (by simpa using hle2))
  have hleK : (1 : ℕ) ≤ K := by
    have h : -(K : ℤ) ≤ -1 := by
      have h' := hle
      rw [hval, WithZero.exp_le_exp] at h'
      exact h'
    omega
  have hKle : K ≤ 1 := by
    have h : ¬ (-(K : ℤ) ≤ -2) := by
      intro hc
      exact hnle (by rw [hval]; exact WithZero.exp_le_exp.mpr hc)
    omega
  have hK1 : K = 1 := le_antisymm hKle hleK
  rw [hval, hK1]
  norm_num

/-- **The concrete lower value**: nu_(2)(2) = 1. -/
theorem sqrtTwoRationalPlace_two_value :
    finitePlaceValueExponent sqrtTwoRationalPlace quadraticExampleTwoUnit = 1 := by
  unfold finitePlaceValueExponent
  have htwo : (quadraticExampleTwoUnit : ℚ) =
      algebraMap (𝓞 ℚ) ℚ (2 : 𝓞 ℚ) := by
    rw [quadraticExampleTwoUnit_val]
    exact (map_natCast (algebraMap (𝓞 ℚ) ℚ) 2).symm
  rw [htwo]
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  rw [sqrtTwoRationalPlace_intValuation_two]
  rw [WithZero.log_exp]
  norm_num


/-! ## Transport at the exact place (sqrt 2), with e = 2 as a theorem -/

/-- The concrete quadratic transport has ramification index two at the exact
upper place (sqrt 2), by the proved arithmetic of
Example36QuadraticRamificationProof. -/
theorem quadraticStrict_ramificationIndex :
    quadraticSquareRootTwoTransport.ramificationIndex sqrtTwoUpperPlace = 2 :=
  quadraticSquareRootTwoTransport_ramificationIndex_eq_two

/-- **The transported finite Delta law at the exact place (sqrt 2)**, with the
proved ramification index two. -/
theorem quadraticStrict_finiteDelta (f : ℚˣ) :
    (numberFieldGlobalPlaceData (F := quadraticExampleField)).finiteDelta
        (unitsMapOfRingHom (algebraMap ℚ quadraticExampleField) f) sqrtTwoUpperPlace =
      (2 : ℤ) * (numberFieldGlobalPlaceData (F := ℚ)).finiteDelta f
        sqrtTwoRationalPlace := by
  have h := quadraticSquareRootTwoTransport_finiteDelta f sqrtTwoUpperPlace
  rw [sqrtTwoUpperPlace_restriction, ramificationIndexAtUpperPlace_sqrtTwo] at h
  exact h

/-- **The Delta law for the concrete unit 2 at the exact place**: the
transported finite value is exactly 2 (ramification index two times the
uniformizer value one). -/
theorem quadraticStrict_two_finiteDelta :
    (numberFieldGlobalPlaceData (F := quadraticExampleField)).finiteDelta
        (unitsMapOfRingHom (algebraMap ℚ quadraticExampleField) quadraticExampleTwoUnit)
        sqrtTwoUpperPlace = 2 := by
  rw [quadraticStrict_finiteDelta]
  rw [numberFieldGlobalPlaceData_finiteDelta, sqrtTwoRationalPlace_two_value]
  norm_num

/-- The finite coordinate of the concrete ideal family at the restricted place
(2). -/
theorem quadraticExampleIdealFamily_finite_sqrtTwo :
    quadraticExampleIdealFamily.finite sqrtTwoRationalPlace =
      finitePlaceValueExponent sqrtTwoRationalPlace quadraticExampleTwoUnit := by
  change principalDivisorFinite quadraticExampleTwoUnit sqrtTwoRationalPlace = _
  exact principalDivisorFinite_apply quadraticExampleTwoUnit sqrtTwoRationalPlace

/-- **Transported concrete ideal family at the exact place**: the finite
coordinate is exactly 2. -/
theorem quadraticStrict_transportedIdealFamily_finite :
    (quadraticSquareRootTwoTransport.transportObject quadraticExampleIdealFamily).finite
        sqrtTwoUpperPlace = 2 := by
  rw [PlaceLocalizationTransport.transportObject_finite_apply]
  rw [quadraticSquareRootTwoTransport_ramificationIndex_eq_two]
  rw [quadraticSquareRootTwoTransport_finitePlaceRestriction]
  rw [sqrtTwoUpperPlace_restriction]
  rw [quadraticExampleIdealFamily_finite_sqrtTwo]
  rw [sqrtTwoRationalPlace_two_value]
  norm_num

/-- **Transported concrete torsor presentation at the exact place**: the finite
coordinate is exactly 2. -/
theorem quadraticStrict_transportedPresentation_finiteCoord :
    (quadraticSquareRootTwoTransport.transportTorsorPresentation
        quadraticExamplePresentation).finiteCoord sqrtTwoUpperPlace = 2 := by
  rw [PlaceLocalizationTransport.transportTorsorPresentation_finiteCoord]
  rw [quadraticSquareRootTwoTransport_ramificationIndex_eq_two]
  rw [quadraticSquareRootTwoTransport_finitePlaceRestriction]
  rw [sqrtTwoUpperPlace_restriction]
  have hcoord : quadraticExamplePresentation.finiteCoord sqrtTwoRationalPlace =
      quadraticExampleIdealFamily.finite sqrtTwoRationalPlace :=
    idealFamilyToPresentation_finiteCoord (numberFieldGlobalPlaceData (F := ℚ))
      quadraticExampleIdealFamily sqrtTwoRationalPlace
  rw [hcoord, quadraticExampleIdealFamily_finite_sqrtTwo, sqrtTwoRationalPlace_two_value]
  norm_num

/-- **Completion valuation exponent at the exact place**: the completion
valuation exponent of the image of 2 is exactly 2. -/
theorem quadraticStrict_completionValuationExponent_two :
    completionValuationExponent sqrtTwoUpperPlace
        (Units.map (algebraMap quadraticExampleField
          (sqrtTwoUpperPlace.adicCompletion quadraticExampleField)).toMonoidHom
          (unitsMapOfRingHom (algebraMap ℚ quadraticExampleField)
            quadraticExampleTwoUnit)) = 2 := by
  rw [← quadraticSquareRootTwoTransport_fieldMap]
  rw [numberFieldTransport_finiteDelta_eq_completionValuationExponent
    quadraticSquareRootTwoTransport quadraticExampleTwoUnit sqrtTwoUpperPlace]
  rw [quadraticSquareRootTwoTransport_ramificationIndex_eq_two]
  rw [quadraticSquareRootTwoTransport_finitePlaceRestriction]
  rw [sqrtTwoUpperPlace_restriction]
  rw [numberFieldGlobalPlaceData_finiteDelta, sqrtTwoRationalPlace_two_value]
  norm_num

/-- **Completion identity at the exact place**: the ramification power of the
lower completion valuation (with the proved exponent two) is the upper
completion valuation of the image. -/
theorem quadraticStrict_completion_valuation_pow
    (x : (upperPlaceRestriction (F := ℚ) sqrtTwoUpperPlace).adicCompletion ℚ) :
    Valued.v x ^ 2 =
      Valued.v (NumberFieldFinitePlace.completionMap (k := ℚ)
        (place := NumberField.FinitePlace.mk sqrtTwoUpperPlace) x) := by
  have h := ofNumberFieldExtension_completion_valuation (F := ℚ)
    (F' := quadraticExampleField) sqrtTwoUpperPlace x
  rw [ramificationIndexAtUpperPlace_sqrtTwo] at h
  exact h

/-! ## What remains

All arithmetic inputs previously recorded as missing are now proved and used:
the exact place (sqrt 2) is constructed, its ramification index over (2) is two,
and the lower value of 2 at (2) is one; consequently the transported finite
coordinates of the concrete ideal family and presentation at (sqrt 2) are
exactly two.  The completion identity holds at that place.

Not claimed: a general ramification formula, the ramification behaviour at the
other places of Q(sqrt 2), any further completion or local-field computation,
a global Frobenioid or Hodge-theater identification, or any theta/q-pilot/Tate
statement. -/

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
