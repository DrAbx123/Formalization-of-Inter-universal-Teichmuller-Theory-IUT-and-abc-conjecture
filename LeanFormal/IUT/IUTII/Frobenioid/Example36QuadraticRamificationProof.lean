import LeanFormal.IUT.IUTII.Frobenioid.Example36QuadraticRamification
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Int
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Tactic

/-!
# Primality of (sqrt 2) and the strict ramification index e = 2 for Q(sqrt 2) / Q

Source anchor: IUT II / Example 3.6 arithmetic of the concrete quadratic number
field Q(sqrt 2); this file discharges the two propositions that the integrated
files Example36QuadraticRamification.lean and Example36TransportInstance.lean
recorded as missing computations:

* quadraticSqrtTwoPrimeMissing : the principal ideal (sqrt 2) is prime in the
  ring of integers of Q(sqrt 2);
* quadraticSqrtTwoRamificationMissing / quadraticRamificationMissingComputation :
  there is an upper place above (2) whose genuine ramification index is two.

Neither statement is assumed; both are proved.  No integrated file is modified.

## Proof route

1. Field norm: for a rational number d that is not a square, the minimal
   polynomial of squareRoot Q d over Q is X^2 - d, obtained from the
   irreducibility of X^2 - d (X_pow_sub_C_irreducible_of_prime) and
   minpoly.eq_of_irreducible_of_monic.  The power basis of the simple extension
   (IntermediateField.adjoin.powerBasis) together with
   Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly then gives the field norm
   Algebra.norm Q (sqrt 2) = -2.
2. The Z-norm vs Q-norm bridge is Mathlib's Algebra.coe_norm_int:
   (Algebra.norm Z x : Q) = Algebra.norm Q (x : K).  Hence
   Algebra.norm Z sqrtTwoInteger = -2, and Ideal.absNorm_span_singleton gives
   Ideal.absNorm (sqrt 2) = 2.
3. Nat.irreducible_iff_nat_prime and
   Ideal.prime_of_irreducible_absNorm_span prove that the element
   sqrtTwoInteger is prime; Ideal.span_singleton_prime upgrades this to
   primality of the principal ideal (sqrt 2).
4. Downstairs: the contraction P = (sqrt 2).under (O_Q) satisfies 2 in P
   (because (sqrt 2)^2 = (2)), and P != top (the upstairs ideal is prime).
   Under the ring equivalence O_Q ~= Z (Rat.ringOfIntegersEquiv) the ideal P
   becomes a proper ideal of Z containing (2); since (2) is maximal in Z
   (Int.ideal_span_isMaximal_of_prime), this forces P = (2)
   (Ideal.IsMaximal.eq_of_le), transferred back along the ring equivalence.
5. Upstairs: Ideal.map (algebraMap O_Q O_K) P = (2) = (sqrt 2)^2, so with
   n = 2, Ideal.ramificationIdx'_spec (lower bound P.map <= Q^2, strict
   failure for Q^3 from Ideal.pow_succ_lt_pow) gives
   Ideal.ramificationIdx' P Q = 2.
6. Unfolding ramificationIndexAtUpperPlace and using
   NumberFieldFinitePlace.comap_maximalIdeal and
   NumberField.FinitePlace.maximalIdeal_mk identifies the ramification index
   at w = HeightOneSpectrum.mk Q with Ideal.ramificationIdx' P Q, hence 2.

## Boundary (not claimed)

* No general ramification formula, no statement about the other places of
  Q(sqrt 2), no completion/local-field computation, and no global
  Frobenioid or theta/q-pilot/Tate identification is claimed.
* The concrete transport is the existing quadraticSquareRootTwoTransport;
  the file only evaluates its ramification index at the place above 2.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open scoped NumberField
open Polynomial IsDedekindDomain
open LeanFormal.IUT.LegendreQuadraticParameterFields

/-! ## The ring of integers and the field norm of sqrt 2 -/

/-- The ring of integers of the concrete quadratic field Q(sqrt 2). -/
abbrev quadraticSqrtTwoIntegers : Type := 𝓞 quadraticSqrtTwoField

/-- The minimal polynomial of a square root of a nonsquare rational number. -/
theorem squareRootMinpoly (d : ℚ) (hd : ¬ IsSquare d) :
    minpoly ℚ (squareRoot ℚ d) = X^2 - C d := by
  have hirr : Irreducible (X ^ 2 - C d) := by
    refine X_pow_sub_C_irreducible_of_prime (p := 2) (by norm_num) (fun b hb => ?_)
    exact hd ⟨b, by rw [pow_two] at hb; exact hb.symm⟩
  have hmonic : (X ^ 2 - C d).Monic := monic_X_pow_sub_C _ (by norm_num)
  have hroot : aeval (squareRoot ℚ d) (X ^ 2 - C d) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, squareRoot_sq]
    exact sub_self _
  exact (minpoly.eq_of_irreducible_of_monic hirr hroot hmonic).symm

/-- The field norm of a square root of a nonsquare rational number is -d. -/
theorem squareRootNorm (d : ℚ) (hd : ¬ IsSquare d) :
    Algebra.norm ℚ (squareRoot ℚ d) = -d := by
  let pb : PowerBasis ℚ (squareRootField ℚ d) :=
    IntermediateField.adjoin.powerBasis (x := algebraicSquareRoot ℚ d)
      (algebraicSquareRoot_isIntegral ℚ d)
  have hgen : pb.gen = squareRoot ℚ d := Subtype.ext rfl
  have hmin : minpoly ℚ pb.gen = X^2 - C d := by
    rw [hgen, squareRootMinpoly d hd]
  have hdim : pb.dim = 2 := by
    rw [← pb.natDegree_minpoly, hmin, Polynomial.natDegree_X_pow_sub_C]
  have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
  rw [hmin, hdim, hgen] at h
  have hcoeff : (X^2 - C d : ℚ[X]).coeff 0 = -d := by simp
  rw [hcoeff] at h
  simpa using h

/-- The field norm of the concrete element sqrt 2 in Q(sqrt 2) is -2. -/
theorem sqrtTwoInFieldNorm : Algebra.norm ℚ sqrtTwoInField = -2 := by
  have hd : ¬ IsSquare (2 : ℚ) := by norm_num
  change Algebra.norm ℚ (squareRoot ℚ (2 : ℚ)) = -2
  exact squareRootNorm (2 : ℚ) hd

/-- sqrtTwoInteger is the image of sqrtTwoInField in the field. -/
theorem sqrtTwoIntegerCoe : (↑sqrtTwoInteger : quadraticSqrtTwoField) = sqrtTwoInField :=
  algebraMap_sqrtTwoInteger

/-- The Z-norm of sqrtTwoInteger is -2. -/
theorem sqrtTwoIntegerNorm : Algebra.norm ℤ sqrtTwoInteger = -2 := by
  have hbridge : Algebra.norm ℚ (↑sqrtTwoInteger : quadraticSqrtTwoField) = -2 := by
    rw [sqrtTwoIntegerCoe, sqrtTwoInFieldNorm]
  have hcast : (Algebra.norm ℤ sqrtTwoInteger : ℚ) = -2 := by
    rw [Algebra.coe_norm_int]
    exact hbridge
  exact Int.cast_injective hcast

/-! ## Primality of the element sqrt 2 and of the ideal (sqrt 2) -/

/-- The concrete ideal (sqrt 2) in the ring of integers of Q(sqrt 2). -/
def sqrtTwoPrincipalIdeal : Ideal quadraticSqrtTwoIntegers :=
  Ideal.span {sqrtTwoInteger}

/-- The element sqrt 2 is nonzero in the ring of integers. -/
theorem sqrtTwoIntegerNeZero : sqrtTwoInteger ≠ 0 := by
  intro h
  exact sqrtTwoInField_ne_zero (by rw [← algebraMap_sqrtTwoInteger, h, map_zero])

/-- The absolute norm of the ideal (sqrt 2) is two. -/
theorem sqrtTwoPrincipalIdealAbsNorm :
    Ideal.absNorm sqrtTwoPrincipalIdeal = 2 := by
  rw [sqrtTwoPrincipalIdeal, Ideal.absNorm_span_singleton, sqrtTwoIntegerNorm]
  norm_num

/-- The element sqrt 2 is prime in the ring of integers. -/
theorem sqrtTwoIntegerPrime : Prime sqrtTwoInteger := by
  refine Ideal.prime_of_irreducible_absNorm_span sqrtTwoIntegerNeZero ?_
  change Irreducible (Ideal.absNorm sqrtTwoPrincipalIdeal)
  rw [sqrtTwoPrincipalIdealAbsNorm]
  exact (Nat.irreducible_iff_nat_prime 2).mpr Nat.prime_two

/-- The principal ideal (sqrt 2) is prime. -/
theorem sqrtTwoPrincipalIdealIsPrime : sqrtTwoPrincipalIdeal.IsPrime :=
  (Ideal.span_singleton_prime sqrtTwoIntegerNeZero).mpr sqrtTwoIntegerPrime

/-- Integrality-free form of the missing proposition: (sqrt 2) is prime. -/
theorem quadraticSqrtTwoPrime_proved : quadraticSqrtTwoPrimeMissing :=
  sqrtTwoPrincipalIdealIsPrime

/-- The ideal (sqrt 2) is not zero. -/
theorem sqrtTwoPrincipalIdealNeBot : sqrtTwoPrincipalIdeal ≠ ⊥ := by
  intro h
  rw [sqrtTwoPrincipalIdeal, Ideal.span_singleton_eq_bot] at h
  exact sqrtTwoIntegerNeZero h

/-! ## The contraction of (sqrt 2) to the integers -/

/-- The ring of integers of Q, identified with Z. -/
abbrev rationalIntegers : Type := 𝓞 ℚ

/-- The ring equivalence between the integers of Q and Z. -/
def rationalIntegersEquiv : rationalIntegers ≃+* ℤ :=
  Rat.ringOfIntegersEquiv

/-- The same ring equivalence as a ring homomorphism. -/
def rationalIntegersHom : rationalIntegers →+* ℤ :=
  rationalIntegersEquiv

/-- The ring homomorphism sends the rational integer two to the integer two. -/
theorem rationalIntegersHom_two : rationalIntegersHom (2 : rationalIntegers) = (2 : ℤ) :=
  map_natCast rationalIntegersHom 2

/-- (2) lies in the contraction of (sqrt 2). -/
theorem twoMemSqrtTwoPrincipalIdealUnder :
    (2 : rationalIntegers) ∈ sqrtTwoPrincipalIdeal.under rationalIntegers := by
  rw [Ideal.mem_under]
  change (2 : quadraticSqrtTwoIntegers) ∈ sqrtTwoPrincipalIdeal
  have h2 : (2 : quadraticSqrtTwoIntegers) ∈ sqrtTwoPrincipalIdeal ^ 2 := by
    rw [sqrtTwoPrincipalIdeal, sqrtTwoIdeal_sq]
    exact Ideal.mem_span_singleton_self _
  exact Ideal.pow_le_self (I := sqrtTwoPrincipalIdeal) (by norm_num : (2:ℕ) ≠ 0) h2

/-- The contraction of (sqrt 2) is a proper ideal. -/
theorem sqrtTwoPrincipalIdealUnderNeTop :
    sqrtTwoPrincipalIdeal.under rationalIntegers ≠ ⊤ := by
  intro htop
  have h1 : (1 : rationalIntegers) ∈ sqrtTwoPrincipalIdeal.under rationalIntegers := by
    rw [htop]
    exact Submodule.mem_top
  rw [Ideal.mem_under] at h1
  have hQ : sqrtTwoPrincipalIdeal = ⊤ :=
    (Ideal.eq_top_iff_one sqrtTwoPrincipalIdeal).mpr (by simpa using h1)
  exact sqrtTwoPrincipalIdealIsPrime.ne_top hQ

theorem comapMapRationalIntegers (I : Ideal rationalIntegers) :
    Ideal.comap rationalIntegersHom (Ideal.map rationalIntegersHom I) = I := by
  have hinj : Function.Injective rationalIntegersHom := rationalIntegersEquiv.injective
  have hsurj : Function.Surjective rationalIntegersHom := rationalIntegersEquiv.surjective
  rw [Ideal.comap_map_of_surjective rationalIntegersHom hsurj,
    Ideal.comap_bot_of_injective rationalIntegersHom hinj, sup_bot_eq]

theorem comapRationalIntegersSpanTwo :
    Ideal.comap rationalIntegersHom (Ideal.span {(2:ℤ)}) =
      Ideal.span {(2 : rationalIntegers)} := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨rationalIntegersEquiv.symm z, ?_⟩
    have hinj : Function.Injective rationalIntegersHom := rationalIntegersEquiv.injective
    refine hinj ?_
    have hsymm : rationalIntegersHom (rationalIntegersEquiv.symm z) = z :=
      RingEquiv.apply_symm_apply rationalIntegersEquiv z
    rw [map_mul, rationalIntegersHom_two, hsymm]
    exact hz
  · rintro ⟨z, hz⟩
    rw [hz, map_mul, rationalIntegersHom_two]
    exact dvd_mul_right 2 _

/-- The contraction of (sqrt 2) to the integers is the ideal (2). -/
theorem sqrtTwoPrincipalIdealUnderEqSpanTwo :
    sqrtTwoPrincipalIdeal.under rationalIntegers = Ideal.span {(2 : rationalIntegers)} := by
  have hinj : Function.Injective rationalIntegersHom := rationalIntegersEquiv.injective
  have hsurj : Function.Surjective rationalIntegersHom := rationalIntegersEquiv.surjective
  have hcomapP : Ideal.comap rationalIntegersHom
      (Ideal.map rationalIntegersHom (sqrtTwoPrincipalIdeal.under rationalIntegers)) =
        sqrtTwoPrincipalIdeal.under rationalIntegers :=
    comapMapRationalIntegers _
  have hcomapS : Ideal.comap rationalIntegersHom
      (Ideal.map rationalIntegersHom (Ideal.span {(2 : rationalIntegers)})) =
        Ideal.span {(2 : rationalIntegers)} :=
    comapMapRationalIntegers _
  have hle : Ideal.span {(2:ℤ)} ≤
      Ideal.map rationalIntegersHom (sqrtTwoPrincipalIdeal.under rationalIntegers) := by
    rw [Ideal.span_singleton_le_iff_mem]
    have h : rationalIntegersHom (2 : rationalIntegers) ∈
        Ideal.map rationalIntegersHom (sqrtTwoPrincipalIdeal.under rationalIntegers) :=
      Ideal.mem_map_of_mem rationalIntegersHom twoMemSqrtTwoPrincipalIdealUnder
    rwa [rationalIntegersHom_two] at h
  have hJne : Ideal.map rationalIntegersHom
      (sqrtTwoPrincipalIdeal.under rationalIntegers) ≠ ⊤ := by
    intro hJtop
    have htop : sqrtTwoPrincipalIdeal.under rationalIntegers = ⊤ := by
      rw [← hcomapP, hJtop]
      exact Ideal.comap_top
    exact sqrtTwoPrincipalIdealUnderNeTop htop
  have hmax : (Ideal.span {(2:ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 2
  have hJ : Ideal.map rationalIntegersHom
      (sqrtTwoPrincipalIdeal.under rationalIntegers) = Ideal.span {(2:ℤ)} :=
    (hmax.eq_of_le hJne hle).symm
  have hmapEq : Ideal.map rationalIntegersHom
        (sqrtTwoPrincipalIdeal.under rationalIntegers) =
      Ideal.map rationalIntegersHom (Ideal.span {(2 : rationalIntegers)}) := by
    rw [hJ, Ideal.map_span, Set.image_singleton, rationalIntegersHom_two]
  have h1 := congrArg (Ideal.comap rationalIntegersHom) hmapEq
  rwa [hcomapP, hcomapS] at h1

/-! ## The ramification index above (2) -/

/-- The image of the contracted ideal upstairs is (sqrt 2)^2 = (2). -/
theorem mapSqrtTwoPrincipalIdealUnder :
    Ideal.map (algebraMap rationalIntegers quadraticSqrtTwoIntegers)
      (sqrtTwoPrincipalIdeal.under rationalIntegers) = sqrtTwoPrincipalIdeal ^ 2 := by
  rw [sqrtTwoPrincipalIdealUnderEqSpanTwo, Ideal.map_span, Set.image_singleton]
  have h2 : algebraMap rationalIntegers quadraticSqrtTwoIntegers (2 : rationalIntegers) =
      (2 : quadraticSqrtTwoIntegers) := map_natCast _ 2
  rw [h2]
  rw [sqrtTwoPrincipalIdeal, sqrtTwoIdeal_sq]

/-- The genuine ideal ramification index of (sqrt 2) above (2) is two. -/
theorem ramificationIdxSqrtTwoPrincipalIdeal :
    Ideal.ramificationIdx' (sqrtTwoPrincipalIdeal.under rationalIntegers)
      sqrtTwoPrincipalIdeal = 2 := by
  haveI : sqrtTwoPrincipalIdeal.IsPrime := sqrtTwoPrincipalIdealIsPrime
  refine Ideal.ramificationIdx'_spec (p := sqrtTwoPrincipalIdeal.under rationalIntegers)
    (P := sqrtTwoPrincipalIdeal) (n := 2) ?_ ?_
  · rw [mapSqrtTwoPrincipalIdealUnder]
  · rw [mapSqrtTwoPrincipalIdealUnder]
    exact not_le_of_gt (Ideal.pow_succ_lt_pow sqrtTwoPrincipalIdealNeBot 2)

/-- The upper place of Q(sqrt 2) above (2) given by the ideal (sqrt 2). -/
def sqrtTwoUpperPlace : HeightOneSpectrum quadraticSqrtTwoIntegers :=
  HeightOneSpectrum.mk sqrtTwoPrincipalIdeal sqrtTwoPrincipalIdealIsPrime
    sqrtTwoPrincipalIdealNeBot

/-- The ramification index of the upper place (sqrt 2) above (2) is two. -/
theorem ramificationIndexAtUpperPlace_sqrtTwo :
    ramificationIndexAtUpperPlace (F := ℚ) (F' := quadraticSqrtTwoField)
      sqrtTwoUpperPlace = 2 := by
  unfold sqrtTwoUpperPlace
  unfold ramificationIndexAtUpperPlace
  rw [LeanFormal.IUT.NumberFieldFinitePlace.comap_maximalIdeal]
  simp only [NumberField.FinitePlace.maximalIdeal_mk]
  exact ramificationIdxSqrtTwoPrincipalIdeal

/-- The concrete transport has ramification index two at the place above (2). -/
theorem quadraticSquareRootTwoTransport_ramificationIndex_eq_two :
    quadraticSquareRootTwoTransport.ramificationIndex sqrtTwoUpperPlace = 2 := by
  rw [quadraticSquareRootTwoTransport_ramificationIndex]
  exact ramificationIndexAtUpperPlace_sqrtTwo

/-- The exact missing computation of Example36QuadraticRamification.lean. -/
theorem quadraticSqrtTwoRamification_proved : quadraticSqrtTwoRamificationMissing :=
  ⟨sqrtTwoUpperPlace, ramificationIndexAtUpperPlace_sqrtTwo⟩

/-- The exact missing computation of Example36TransportInstance.lean. -/
theorem quadraticRamificationMissingComputation_proved :
    quadraticRamificationMissingComputation :=
  ⟨sqrtTwoUpperPlace, ramificationIndexAtUpperPlace_sqrtTwo⟩

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
