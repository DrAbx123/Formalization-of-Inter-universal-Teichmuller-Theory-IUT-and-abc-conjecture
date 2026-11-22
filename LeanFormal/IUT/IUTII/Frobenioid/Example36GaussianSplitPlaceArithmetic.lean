import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianIntegralBasis
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteFinitePlaceBoundary
import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Lattice
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.NumberField.Basic
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalInputs
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalStructureInstances
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Field.ZMod

/-!
# Gaussian split-place arithmetic at 5 (task-119)

This file develops the actual Gaussian split-place arithmetic needed by task-108
route (a), in the standard Mathlib Gaussian-integer model GaussianInt = Zsqrtd (-1):

* the actual Gaussian prime generator 2 + i and its conjugate 2 - i;
* the actual factorization (2 + i)(2 - i) = 5 in GaussianInt;
* the induced principal-ideal factorization (5) = (2+i)(2-i);
* the norm computation norm(2+i) = 5.

## Status of task-119 (superseding note, n8-layer1-build-20261020)

The paragraph that previously stood here said that the ring-of-integers
equivalence with `NumberField.RingOfIntegers (AdjoinRoot (X^2+1))`, the
irreducibility/maximality and residue quotient `GaussianInt/(2+i) = ZMod 5`,
and the transport to `concreteGaussianFivePlace` were "NOT yet proved here".
That statement is superseded by the material now present:

* the ring-of-integers equivalence `GaussianInt ≃+* NumberField.RingOfIntegers
  (AdjoinRoot (X^2+1))` and its inverse/`algebraMap` laws are in
  `Example36GaussianIntegralBasis` (`gaussianIntEquivRingOfIntegers`);
* irreducibility of `X^2+1`, maximality of `(2+i)` and `(2-i)`, and the residue
  quotient equivalences `GaussianInt/(2±i) ≃+* ZMod 5` (with computation rules
  `..._mk`) are proved in this file;
* the transport to `concreteGaussianFivePlace` is proved in the last section:
  the chosen maximal ideal is one of the two primes over 5, its residue field is
  `ZMod 5` with five elements and residue characteristic 5, its relative
  ramification index and residue degree are one, the completion degree is one,
  and the 5-adic valuation of a rational number equals its valuation at the
  chosen place (the `e = 1` normalization), both before and after completion.

What this construction genuinely does not determine is which of the two primes
over 5 the classical choice `concreteGaussianFivePlace` selects; the statements
are therefore kept uniform in the prime.  No card/refl assumption is introduced.
-/

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36

local instance gaussianSplitFivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

local instance gaussianSplitGaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  Fact.mk (by
    apply X_pow_sub_C_irreducible_of_prime (p := 2) Nat.prime_two
    intro b hb
    have hnonneg : 0 ≤ b ^ 2 := sq_nonneg b
    rw [hb] at hnonneg
    exact (not_le_of_gt (neg_lt_zero.mpr zero_lt_one)) hnonneg)

/-- The polynomial `X^2 + 1` is irreducible over ℚ: 2 is prime and -1 is not a
square in ℚ.  This is the named form of the local fact instance above. -/
theorem gaussianSplitFivePolynomial_irreducible :
    Irreducible (Polynomial.X ^ 2 + 1 : Polynomial ℚ) := by
  have h : Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ) :=
    gaussianSplitGaussianIrreducible.out
  simpa using h

/-- The Gaussian prime generator 2 + i. -/
abbrev gaussianIntFiveGenerator : GaussianInt := ⟨2, 1⟩

/-- The conjugate Gaussian prime generator 2 - i. -/
abbrev gaussianIntFiveConjugate : GaussianInt := ⟨2, -1⟩

/-- The actual norm computation: norm(2 + i) = 5. -/
theorem gaussianIntFiveGenerator_norm :
    Zsqrtd.norm gaussianIntFiveGenerator = 5 := by
  simp [gaussianIntFiveGenerator, Zsqrtd.norm_def]

/-- The actual Gaussian factorization (2 + i)(2 - i) = 5. -/
theorem gaussianIntFiveGenerator_mul_conjugate :
    gaussianIntFiveGenerator * gaussianIntFiveConjugate = (5 : GaussianInt) := by
  apply Zsqrtd.ext_iff.mpr
  constructor <;> norm_num [gaussianIntFiveGenerator, gaussianIntFiveConjugate]

/-- The actual principal-ideal factorization (5) = (2+i)(2-i). -/
theorem gaussianIntFive_ideal_factorization :
    Ideal.span {(5 : GaussianInt)} =
      Ideal.span {gaussianIntFiveGenerator} *
        Ideal.span {gaussianIntFiveConjugate} := by
  rw [← gaussianIntFiveGenerator_mul_conjugate]
  exact (Ideal.span_singleton_mul_span_singleton _ _).symm

/-- 5 lies in the ideal (2+i): the ideal above 5 containing the Gaussian prime. -/
theorem gaussianInt_five_mem_generator_ideal :
    (5 : GaussianInt) ∈ Ideal.span {gaussianIntFiveGenerator} := by
  rw [← gaussianIntFiveGenerator_mul_conjugate]
  exact Ideal.mul_mem_right gaussianIntFiveConjugate _
    (Ideal.subset_span (Set.mem_singleton_iff.mpr rfl))


/-- The prime generator 2+i is irreducible: its norm is the prime 5, and a
factorization would force one factor to have norm one, hence to be a unit. -/
theorem gaussianIntFiveGenerator_irreducible :
    Irreducible gaussianIntFiveGenerator := by
  rw [irreducible_iff]
  constructor
  · intro hunit
    have hnorm : (Zsqrtd.norm gaussianIntFiveGenerator).natAbs = 1 :=
      Zsqrtd.norm_eq_one_iff.mpr hunit
    rw [gaussianIntFiveGenerator_norm] at hnorm
    norm_num at hnorm
  · intro a b hab
    have hnorm : (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs = 5 := by
      calc (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs
          = (Zsqrtd.norm (a * b)).natAbs := by rw [Zsqrtd.norm_mul, Int.natAbs_mul]
        _ = (Zsqrtd.norm gaussianIntFiveGenerator).natAbs := by rw [hab]
        _ = 5 := by rw [gaussianIntFiveGenerator_norm]; norm_num
    have hdvd : (Zsqrtd.norm a).natAbs ∣ 5 := ⟨(Zsqrtd.norm b).natAbs, hnorm.symm⟩
    have hcases := (Nat.prime_five).eq_one_or_self_of_dvd ((Zsqrtd.norm a).natAbs) hdvd
    rcases hcases with ha | ha
    · left
      exact Zsqrtd.norm_eq_one_iff.mp ha
    · right
      have hb : (Zsqrtd.norm b).natAbs = 1 := by
        rw [ha] at hnorm
        omega
      exact Zsqrtd.norm_eq_one_iff.mp hb

/-- The ideal (2+i) is maximal in the Gaussian integers: the Gaussian integers
form a principal ideal domain and 2+i is irreducible. -/
theorem gaussianIntFiveGenerator_ideal_isMaximal :
    (Ideal.span {gaussianIntFiveGenerator}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible gaussianIntFiveGenerator_irreducible

/-- The actual residue map GaussianInt -> ZMod 5 sending i to 3 (a square root
of -1 modulo 5), constructed by the universal property of Zsqrtd.lift. -/
noncomputable def gaussianIntFiveResidueMap : GaussianInt →+* ZMod 5 :=
  Zsqrtd.lift ⟨(3 : ZMod 5), by decide⟩

/-- The residue map kills 2+i: 2 + 1*3 = 5 = 0 in ZMod 5. -/
theorem gaussianIntFiveResidueMap_generator :
    gaussianIntFiveResidueMap gaussianIntFiveGenerator = 0 := by
  simp [gaussianIntFiveResidueMap, gaussianIntFiveGenerator]
  decide

/-- The residue map is surjective: its values on integers already exhaust
ZMod 5. -/
theorem gaussianIntFiveResidueMap_surjective :
    Function.Surjective gaussianIntFiveResidueMap := by
  intro y
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective y
  refine ⟨(a : GaussianInt), ?_⟩
  simp [gaussianIntFiveResidueMap, Zsqrtd.lift_apply_apply]

/-- The ideal (2+i) is contained in the kernel of the residue map. -/
theorem gaussianIntFiveGenerator_ideal_le_ker :
    Ideal.span {gaussianIntFiveGenerator} ≤
      RingHom.ker gaussianIntFiveResidueMap := by
  refine Ideal.span_le.mpr ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact (RingHom.mem_ker).mpr gaussianIntFiveResidueMap_generator

/-- The kernel of the residue map is exactly the ideal (2+i). -/
theorem gaussianIntFiveResidueMap_ker :
    RingHom.ker gaussianIntFiveResidueMap =
      Ideal.span {gaussianIntFiveGenerator} := by
  have hker : (RingHom.ker gaussianIntFiveResidueMap).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective gaussianIntFiveResidueMap
      gaussianIntFiveResidueMap_surjective
  exact (Ideal.IsMaximal.eq_of_le gaussianIntFiveGenerator_ideal_isMaximal hker.ne_top
    gaussianIntFiveGenerator_ideal_le_ker).symm

/-- The actual residue quotient equivalence GaussianInt/(2+i) ≃+* ZMod 5. -/
noncomputable def gaussianIntFiveResidueEquiv :
    (GaussianInt ⧸ Ideal.span {gaussianIntFiveGenerator}) ≃+* ZMod 5 :=
  (Ideal.quotEquivOfEq gaussianIntFiveResidueMap_ker.symm).trans
    (RingHom.quotientKerEquivOfSurjective gaussianIntFiveResidueMap_surjective)

/-- Computation rule for the residue equivalence at (2+i): on the class of a
Gaussian integer it is the explicit residue map. -/
theorem gaussianIntFiveResidueEquiv_mk (z : GaussianInt) :
    gaussianIntFiveResidueEquiv
        (Ideal.Quotient.mk (Ideal.span {gaussianIntFiveGenerator}) z) =
      gaussianIntFiveResidueMap z := by
  rw [gaussianIntFiveResidueEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- The ring of integers of the Gaussian field, as a type synonym. -/
abbrev gaussianRingOfIntegers : Type := NumberField.RingOfIntegers GaussianField

instance gaussianIntFiveGenerator_ideal_isMaximal_instance :
    (Ideal.span {gaussianIntFiveGenerator}).IsMaximal :=
  gaussianIntFiveGenerator_ideal_isMaximal

/-- Norm of the conjugate Gaussian prime 2-i. -/
theorem gaussianIntFiveConjugate_norm :
    Zsqrtd.norm gaussianIntFiveConjugate = 5 := by
  simp [gaussianIntFiveConjugate, Zsqrtd.norm_def]

/-- The conjugate Gaussian prime 2-i is irreducible. -/
theorem gaussianIntFiveConjugate_irreducible :
    Irreducible gaussianIntFiveConjugate := by
  rw [irreducible_iff]
  constructor
  · intro hunit
    have hnorm : (Zsqrtd.norm gaussianIntFiveConjugate).natAbs = 1 :=
      Zsqrtd.norm_eq_one_iff.mpr hunit
    rw [gaussianIntFiveConjugate_norm] at hnorm
    norm_num at hnorm
  · intro a b hab
    have hnorm : (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs = 5 := by
      calc (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs
          = (Zsqrtd.norm (a * b)).natAbs := by rw [Zsqrtd.norm_mul, Int.natAbs_mul]
        _ = (Zsqrtd.norm gaussianIntFiveConjugate).natAbs := by rw [hab]
        _ = 5 := by rw [gaussianIntFiveConjugate_norm]; norm_num
    have hdvd : (Zsqrtd.norm a).natAbs ∣ 5 := ⟨(Zsqrtd.norm b).natAbs, hnorm.symm⟩
    have hcases := (Nat.prime_five).eq_one_or_self_of_dvd ((Zsqrtd.norm a).natAbs) hdvd
    rcases hcases with ha | ha
    · left
      exact Zsqrtd.norm_eq_one_iff.mp ha
    · right
      have hb : (Zsqrtd.norm b).natAbs = 1 := by
        rw [ha] at hnorm
        omega
      exact Zsqrtd.norm_eq_one_iff.mp hb

/-- The conjugate ideal (2-i) is maximal. -/
instance gaussianIntFiveConjugate_ideal_isMaximal :
    (Ideal.span {gaussianIntFiveConjugate}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible gaussianIntFiveConjugate_irreducible



/-- The residue map GaussianInt → ZMod 5 at the conjugate prime 2-i, sending
i to the other square root 2 of -1 modulo 5. -/
noncomputable def gaussianIntFiveConjugateResidueMap : GaussianInt →+* ZMod 5 :=
  Zsqrtd.lift ⟨(2 : ZMod 5), by decide⟩

/-- The conjugate residue map kills 2-i: 2 - 1*2 = 0 in ZMod 5. -/
theorem gaussianIntFiveConjugateResidueMap_generator :
    gaussianIntFiveConjugateResidueMap gaussianIntFiveConjugate = 0 := by
  simp [gaussianIntFiveConjugateResidueMap, gaussianIntFiveConjugate]

/-- The conjugate residue map is surjective, already on the integer classes. -/
theorem gaussianIntFiveConjugateResidueMap_surjective :
    Function.Surjective gaussianIntFiveConjugateResidueMap := by
  intro y
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective y
  refine ⟨(a : GaussianInt), ?_⟩
  simp [gaussianIntFiveConjugateResidueMap]

/-- The ideal (2-i) is contained in the kernel of the conjugate residue map. -/
theorem gaussianIntFiveConjugate_ideal_le_ker :
    Ideal.span {gaussianIntFiveConjugate} ≤
      RingHom.ker gaussianIntFiveConjugateResidueMap := by
  refine Ideal.span_le.mpr ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact (RingHom.mem_ker).mpr gaussianIntFiveConjugateResidueMap_generator

/-- The kernel of the conjugate residue map is exactly the ideal (2-i). -/
theorem gaussianIntFiveConjugateResidueMap_ker :
    RingHom.ker gaussianIntFiveConjugateResidueMap =
      Ideal.span {gaussianIntFiveConjugate} := by
  have hker : (RingHom.ker gaussianIntFiveConjugateResidueMap).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective gaussianIntFiveConjugateResidueMap
      gaussianIntFiveConjugateResidueMap_surjective
  exact (Ideal.IsMaximal.eq_of_le gaussianIntFiveConjugate_ideal_isMaximal hker.ne_top
    gaussianIntFiveConjugate_ideal_le_ker).symm

/-- The actual residue quotient equivalence GaussianInt/(2-i) ≃+* ZMod 5. -/
noncomputable def gaussianIntFiveConjugateResidueEquiv :
    (GaussianInt ⧸ Ideal.span {gaussianIntFiveConjugate}) ≃+* ZMod 5 :=
  (Ideal.quotEquivOfEq gaussianIntFiveConjugateResidueMap_ker.symm).trans
    (RingHom.quotientKerEquivOfSurjective gaussianIntFiveConjugateResidueMap_surjective)

/-- Computation rule for the residue equivalence at (2-i). -/
theorem gaussianIntFiveConjugateResidueEquiv_mk (z : GaussianInt) :
    gaussianIntFiveConjugateResidueEquiv
        (Ideal.Quotient.mk (Ideal.span {gaussianIntFiveConjugate}) z) =
      gaussianIntFiveConjugateResidueMap z := by
  rw [gaussianIntFiveConjugateResidueEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]


/-- The explicit Gaussian prime ideal (2+i) transported to the ring of integers
of the Gaussian field via the actual ring-of-integers equivalence. -/
noncomputable def gaussianFieldFivePrimePlus : Ideal gaussianRingOfIntegers :=
  Ideal.comap gaussianRingOfIntegersEquivGaussianInt.toRingHom
    (Ideal.span {gaussianIntFiveGenerator})

/-- The transported Gaussian prime (2+i) is maximal. -/
instance gaussianFieldFivePrimePlus_isMaximal :
    gaussianFieldFivePrimePlus.IsMaximal :=
  Ideal.comap_isMaximal_of_equiv gaussianRingOfIntegersEquivGaussianInt

/-- The actual residue quotient of the transported Gaussian prime (2+i) is
ZMod 5, obtained by transporting the GaussianInt quotient along the ring-of-
integers equivalence. -/
noncomputable def gaussianFieldFivePrimePlusResidueEquiv :
    (gaussianRingOfIntegers ⧸ gaussianFieldFivePrimePlus) ≃+* ZMod 5 :=
  (Ideal.quotientEquiv (gaussianFieldFivePrimePlus)
    (Ideal.span {gaussianIntFiveGenerator})
    gaussianRingOfIntegersEquivGaussianInt
    (by
      change Ideal.span {gaussianIntFiveGenerator} =
        Ideal.map gaussianRingOfIntegersEquivGaussianInt.toRingHom
          gaussianFieldFivePrimePlus
      rw [gaussianFieldFivePrimePlus,
        Ideal.map_comap_of_surjective
          gaussianRingOfIntegersEquivGaussianInt.toRingHom
          gaussianRingOfIntegersEquivGaussianInt.surjective])).trans
    gaussianIntFiveResidueEquiv

/-- Computation rule for the transported plus residue equivalence: on the class
of an integral element it is the Gaussian residue map of its image in Z[i]. -/
theorem gaussianFieldFivePrimePlusResidueEquiv_mk
    (x : gaussianRingOfIntegers) :
    gaussianFieldFivePrimePlusResidueEquiv
        (Ideal.Quotient.mk gaussianFieldFivePrimePlus x) =
      gaussianIntFiveResidueMap (gaussianRingOfIntegersEquivGaussianInt x) := by
  rw [gaussianFieldFivePrimePlusResidueEquiv, RingEquiv.trans_apply,
    Ideal.quotientEquiv_mk, gaussianIntFiveResidueEquiv_mk]


/-- The conjugate prime (2-i) transported to the ring of integers. -/
noncomputable def gaussianFieldFivePrimeMinus : Ideal gaussianRingOfIntegers :=
  Ideal.comap gaussianRingOfIntegersEquivGaussianInt.toRingHom
    (Ideal.span {gaussianIntFiveConjugate})

/-- The transported conjugate prime is maximal. -/
instance gaussianFieldFivePrimeMinus_isMaximal :
    gaussianFieldFivePrimeMinus.IsMaximal :=
  Ideal.comap_isMaximal_of_equiv gaussianRingOfIntegersEquivGaussianInt

/-- The actual residue quotient of the transported conjugate prime (2-i) is
ZMod 5, obtained by transporting the GaussianInt quotient along the ring-of-
integers equivalence. -/
noncomputable def gaussianFieldFivePrimeMinusResidueEquiv :
    (gaussianRingOfIntegers ⧸ gaussianFieldFivePrimeMinus) ≃+* ZMod 5 :=
  (Ideal.quotientEquiv (gaussianFieldFivePrimeMinus)
    (Ideal.span {gaussianIntFiveConjugate})
    gaussianRingOfIntegersEquivGaussianInt
    (by
      change Ideal.span {gaussianIntFiveConjugate} =
        Ideal.map gaussianRingOfIntegersEquivGaussianInt.toRingHom
          gaussianFieldFivePrimeMinus
      rw [gaussianFieldFivePrimeMinus,
        Ideal.map_comap_of_surjective
          gaussianRingOfIntegersEquivGaussianInt.toRingHom
          gaussianRingOfIntegersEquivGaussianInt.surjective])).trans
    gaussianIntFiveConjugateResidueEquiv

/-- Computation rule for the transported minus residue equivalence. -/
theorem gaussianFieldFivePrimeMinusResidueEquiv_mk
    (x : gaussianRingOfIntegers) :
    gaussianFieldFivePrimeMinusResidueEquiv
        (Ideal.Quotient.mk gaussianFieldFivePrimeMinus x) =
      gaussianIntFiveConjugateResidueMap (gaussianRingOfIntegersEquivGaussianInt x) := by
  rw [gaussianFieldFivePrimeMinusResidueEquiv, RingEquiv.trans_apply,
    Ideal.quotientEquiv_mk, gaussianIntFiveConjugateResidueEquiv_mk]

/-- Factorization of the principal ideal (5) in the ring of integers of the
Gaussian field as the product of the two transported Gaussian primes. -/
theorem gaussianFieldFive_ideal_factorization :
    Ideal.span {(5 : gaussianRingOfIntegers)} =
      gaussianFieldFivePrimePlus * gaussianFieldFivePrimeMinus := by
  have hmap : Ideal.map gaussianRingOfIntegersEquivGaussianInt.toRingHom
        (Ideal.span {(5 : gaussianRingOfIntegers)}) =
      Ideal.map gaussianRingOfIntegersEquivGaussianInt.toRingHom
        (gaussianFieldFivePrimePlus * gaussianFieldFivePrimeMinus) := by
    rw [Ideal.map_mul]
    rw [gaussianFieldFivePrimePlus, gaussianFieldFivePrimeMinus]
    rw [Ideal.map_comap_of_surjective
        (f := gaussianRingOfIntegersEquivGaussianInt.toRingHom)
        gaussianRingOfIntegersEquivGaussianInt.surjective,
      Ideal.map_comap_of_surjective
        (f := gaussianRingOfIntegersEquivGaussianInt.toRingHom)
        gaussianRingOfIntegersEquivGaussianInt.surjective]
    rw [Ideal.map_span]
    simp only [Set.image_singleton]
    have hfive : gaussianRingOfIntegersEquivGaussianInt.toRingHom
        (5 : gaussianRingOfIntegers) = (5 : GaussianInt) :=
      map_natCast _ 5
    rw [hfive]
    exact gaussianIntFive_ideal_factorization
  have h := congrArg (Ideal.comap gaussianRingOfIntegersEquivGaussianInt.toRingHom) hmap
  rw [Ideal.comap_map_of_bijective (f := gaussianRingOfIntegersEquivGaussianInt.toRingHom)
      gaussianRingOfIntegersEquivGaussianInt.bijective,
    Ideal.comap_map_of_bijective (f := gaussianRingOfIntegersEquivGaussianInt.toRingHom)
      gaussianRingOfIntegersEquivGaussianInt.bijective] at h
  exact h


/-- Classification of primes containing (5): an ideal P with (5) <= P is one of
the two transported Gaussian primes. -/
theorem gaussianFieldFivePrime_classification
    (P : Ideal gaussianRingOfIntegers) [hP : P.IsPrime]
    (h5 : Ideal.span {(5 : gaussianRingOfIntegers)} ≤ P) :
    P = gaussianFieldFivePrimePlus ∨ P = gaussianFieldFivePrimeMinus := by
  have hle : gaussianFieldFivePrimePlus * gaussianFieldFivePrimeMinus ≤ P := by
    rw [← gaussianFieldFive_ideal_factorization]
    exact h5
  rcases (Ideal.IsPrime.mul_le hP).mp hle with h | h
  · left
    exact (gaussianFieldFivePrimePlus_isMaximal.eq_of_le hP.ne_top h).symm
  · right
    exact (gaussianFieldFivePrimeMinus_isMaximal.eq_of_le hP.ne_top h).symm

/-- The concrete place over 5 has its maximal ideal under the rational integers
equal to the concrete height-one prime at 5. -/
theorem concreteGaussianFivePlace_under_eq :
    ((concreteGaussianFivePlace.maximalIdeal : Ideal gaussianRingOfIntegers)).under
        (NumberField.RingOfIntegers ℚ) = concreteFiveHeightOne.asIdeal := by
  rw [Ideal.under_def]
  have h := NumberFieldFinitePlace.comap_maximalIdeal (k := ℚ) concreteGaussianFivePlace
  rw [concreteGaussianFivePlace_comap, concreteFivePlace_maximalIdeal] at h
  exact h.symm

/-- The integer 5 lies in the maximal ideal of the concrete place over 5. -/
theorem concreteGaussianFivePlace_five_mem :
    (5 : gaussianRingOfIntegers) ∈
      (concreteGaussianFivePlace.maximalIdeal : Ideal gaussianRingOfIntegers) := by
  have hunder := concreteGaussianFivePlace_under_eq
  have h5 : (5 : NumberField.RingOfIntegers ℚ) ∈ concreteFiveHeightOne.asIdeal :=
    concreteFiveHeightOne_five_mem
  have hmem : algebraMap (NumberField.RingOfIntegers ℚ) gaussianRingOfIntegers
      (5 : NumberField.RingOfIntegers ℚ) ∈
      (concreteGaussianFivePlace.maximalIdeal : Ideal gaussianRingOfIntegers) := by
    rw [← Ideal.mem_under]
    rw [hunder]
    exact h5
  have hmap : algebraMap (NumberField.RingOfIntegers ℚ) gaussianRingOfIntegers
      (5 : NumberField.RingOfIntegers ℚ) = (5 : gaussianRingOfIntegers) :=
    map_natCast _ 5
  rw [hmap] at hmem
  exact hmem

/-- The maximal ideal of the concrete place over 5 is one of the two transported
Gaussian primes. -/
theorem concreteGaussianFivePlace_maximalIdeal_eq_plus_or_minus :
    (concreteGaussianFivePlace.maximalIdeal : Ideal gaussianRingOfIntegers) =
        gaussianFieldFivePrimePlus ∨
      (concreteGaussianFivePlace.maximalIdeal : Ideal gaussianRingOfIntegers) =
        gaussianFieldFivePrimeMinus := by
  haveI : (concreteGaussianFivePlace.maximalIdeal : Ideal gaussianRingOfIntegers).IsPrime :=
    concreteGaussianFivePlace.maximalIdeal.isPrime
  exact gaussianFieldFivePrime_classification _
    (Ideal.span_le.mpr (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact concreteGaussianFivePlace_five_mem))


/-- The generator 2+i does not divide 2-i in the Gaussian integers. -/
theorem gaussianIntFiveGenerator_not_dvd_conjugate :
    ¬ gaussianIntFiveGenerator ∣ gaussianIntFiveConjugate := by
  intro h
  obtain ⟨c, hc⟩ := h
  have h2 : gaussianIntFiveConjugate * gaussianIntFiveConjugate =
      (5 : GaussianInt) * c := by
    calc gaussianIntFiveConjugate * gaussianIntFiveConjugate
        = (gaussianIntFiveGenerator * gaussianIntFiveConjugate) * c := by
          rw [hc]; ring
      _ = (5 : GaussianInt) * c := by
          rw [gaussianIntFiveGenerator_mul_conjugate]
  have hre := congrArg Zsqrtd.re h2
  norm_num [gaussianIntFiveConjugate, Zsqrtd.re_mul, Zsqrtd.re_intCast] at hre
  omega

/-- The two transported primes are distinct. -/
theorem gaussianFieldFivePrimePlus_ne_minus :
    gaussianFieldFivePrimePlus ≠ gaussianFieldFivePrimeMinus := by
  intro h
  have hmap : Ideal.span {gaussianIntFiveGenerator} =
      Ideal.span {gaussianIntFiveConjugate} := by
    have := congrArg
      (Ideal.map gaussianRingOfIntegersEquivGaussianInt.toRingHom) h
    rwa [gaussianFieldFivePrimePlus, gaussianFieldFivePrimeMinus,
      Ideal.map_comap_of_surjective
        (f := gaussianRingOfIntegersEquivGaussianInt.toRingHom)
        gaussianRingOfIntegersEquivGaussianInt.surjective,
      Ideal.map_comap_of_surjective
        (f := gaussianRingOfIntegersEquivGaussianInt.toRingHom)
        gaussianRingOfIntegersEquivGaussianInt.surjective] at this
  have hmem : gaussianIntFiveConjugate ∈ Ideal.span {gaussianIntFiveGenerator} := by
    rw [hmap]
    exact Ideal.subset_span (Set.mem_singleton_iff.mpr rfl)
  exact gaussianIntFiveGenerator_not_dvd_conjugate (Ideal.mem_span_singleton.mp hmem)


/-- Finrank of the Gaussian field over Q is two. -/
theorem gaussianField_finrank : Module.finrank ℚ GaussianField = 2 := by
  have hf : gaussianPolynomial ≠ 0 := gaussianPolynomial_monic.ne_zero
  change Module.finrank ℚ (AdjoinRoot gaussianPolynomial) = 2
  rw [show Module.finrank ℚ (AdjoinRoot gaussianPolynomial) =
      (AdjoinRoot.powerBasis (f := gaussianPolynomial) hf).dim from
        (AdjoinRoot.powerBasis (f := gaussianPolynomial) hf).finrank]
  rw [AdjoinRoot.powerBasis_dim]
  simpa [gaussianPolynomial] using (Polynomial.natDegree_X_pow_sub_C (n := 2) (r := (-1 : ℚ)))

/-- The ring-of-integers equivalence is compatible with integer algebra maps. -/
theorem gaussianRingOfIntegersEquivGaussianInt_algebraMap_int (z : ℤ) :
    gaussianRingOfIntegersEquivGaussianInt
        (algebraMap ℤ gaussianRingOfIntegers z) =
      algebraMap ℤ GaussianInt z := by
  apply IsIntegralClosure.algebraMap_injective GaussianInt ℤ GaussianField
  rw [gaussianRingOfIntegersEquivGaussianInt_algebraMap]
  rw [← IsScalarTower.algebraMap_apply ℤ gaussianRingOfIntegers GaussianField,
    ← IsScalarTower.algebraMap_apply ℤ GaussianInt GaussianField]

/-- The ideal generated by 2+i lies over the rational prime ideal (5). -/
theorem gaussianIntFiveGenerator_ideal_under :
    (Ideal.span {gaussianIntFiveGenerator}).under ℤ = Ideal.span {(5 : ℤ)} := by
  have hle : Ideal.span {(5 : ℤ)} ≤ (Ideal.span {gaussianIntFiveGenerator}).under ℤ := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    change (5 : ℤ) ∈ Ideal.comap (algebraMap ℤ GaussianInt)
      (Ideal.span {gaussianIntFiveGenerator})
    rw [Ideal.mem_comap]
    simpa using gaussianInt_five_mem_generator_ideal
  have hne : (Ideal.span {gaussianIntFiveGenerator}).under ℤ ≠ ⊤ := by
    intro h
    have h1 : (1 : ℤ) ∈ (Ideal.span {gaussianIntFiveGenerator}).under ℤ := by
      rw [h]; exact Submodule.mem_top
    change (1 : ℤ) ∈ Ideal.comap (algebraMap ℤ GaussianInt)
      (Ideal.span {gaussianIntFiveGenerator}) at h1
    rw [Ideal.mem_comap] at h1
    have hone : (1 : GaussianInt) ∈ Ideal.span {gaussianIntFiveGenerator} := by
      simpa using h1
    have htop : (⊤ : Ideal GaussianInt) ≤ Ideal.span {gaussianIntFiveGenerator} := by
      rw [top_le_iff, Ideal.eq_top_iff_one]
      exact hone
    exact gaussianIntFiveGenerator_ideal_isMaximal_instance.ne_top (top_le_iff.mp htop)
  exact (Ideal.IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime 5) hne hle).symm

/-- The conjugate ideal (2-i) lies over (5). -/
theorem gaussianIntFiveConjugate_ideal_under :
    (Ideal.span {gaussianIntFiveConjugate}).under ℤ = Ideal.span {(5 : ℤ)} := by
  have h5conj : (5 : GaussianInt) ∈ Ideal.span {gaussianIntFiveConjugate} := by
    rw [Ideal.mem_span_singleton]
    exact ⟨gaussianIntFiveGenerator, by
      rw [mul_comm, gaussianIntFiveGenerator_mul_conjugate]⟩
  have hle : Ideal.span {(5 : ℤ)} ≤ (Ideal.span {gaussianIntFiveConjugate}).under ℤ := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    change (5 : ℤ) ∈ Ideal.comap (algebraMap ℤ GaussianInt)
      (Ideal.span {gaussianIntFiveConjugate})
    rw [Ideal.mem_comap]
    simpa using h5conj
  have hne : (Ideal.span {gaussianIntFiveConjugate}).under ℤ ≠ ⊤ := by
    intro h
    have h1 : (1 : ℤ) ∈ (Ideal.span {gaussianIntFiveConjugate}).under ℤ := by
      rw [h]; exact Submodule.mem_top
    change (1 : ℤ) ∈ Ideal.comap (algebraMap ℤ GaussianInt)
      (Ideal.span {gaussianIntFiveConjugate}) at h1
    rw [Ideal.mem_comap] at h1
    have hone : (1 : GaussianInt) ∈ Ideal.span {gaussianIntFiveConjugate} := by
      simpa using h1
    have htop : (⊤ : Ideal GaussianInt) ≤ Ideal.span {gaussianIntFiveConjugate} := by
      rw [top_le_iff, Ideal.eq_top_iff_one]
      exact hone
    exact gaussianIntFiveConjugate_ideal_isMaximal.ne_top (top_le_iff.mp htop)
  exact (Ideal.IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime 5) hne hle).symm

/-- The transported plus prime lies over (5). -/
theorem gaussianFieldFivePrimePlus_under :
    (gaussianFieldFivePrimePlus).under ℤ = Ideal.span {(5 : ℤ)} := by
  have hp5 : (Ideal.span {(5 : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by norm_num : (5 : ℤ) ≠ 0)]
    rw [Int.prime_iff_natAbs_prime]
    norm_num
  have hp5_ne : (Ideal.span {(5 : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    norm_num
  have h5mem : (5 : gaussianRingOfIntegers) ∈ gaussianFieldFivePrimePlus := by
    rw [gaussianFieldFivePrimePlus, Ideal.mem_comap]
    have hfive : gaussianRingOfIntegersEquivGaussianInt.toRingHom
        (5 : gaussianRingOfIntegers) = (5 : GaussianInt) := map_natCast _ 5
    rw [hfive]
    exact gaussianInt_five_mem_generator_ideal
  have hle : Ideal.span {(5 : ℤ)} ≤ (gaussianFieldFivePrimePlus).under ℤ := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    change (5 : ℤ) ∈ Ideal.comap (algebraMap ℤ gaussianRingOfIntegers)
      gaussianFieldFivePrimePlus
    rw [Ideal.mem_comap]
    simpa using h5mem
  have hne : (gaussianFieldFivePrimePlus).under ℤ ≠ ⊤ := by
    intro h
    have h1 : (1 : ℤ) ∈ (gaussianFieldFivePrimePlus).under ℤ := by
      rw [h]; exact Submodule.mem_top
    change (1 : ℤ) ∈ Ideal.comap (algebraMap ℤ gaussianRingOfIntegers)
      gaussianFieldFivePrimePlus at h1
    rw [Ideal.mem_comap] at h1
    have hone : (1 : gaussianRingOfIntegers) ∈ gaussianFieldFivePrimePlus := by
      simpa using h1
    have htop : (⊤ : Ideal gaussianRingOfIntegers) ≤ gaussianFieldFivePrimePlus := by
      rw [top_le_iff, Ideal.eq_top_iff_one]
      exact hone
    exact gaussianFieldFivePrimePlus_isMaximal.ne_top (top_le_iff.mp htop)
  exact (Ideal.IsMaximal.eq_of_le (hp5.isMaximal hp5_ne) hne hle).symm

/-- The transported minus prime lies over (5). -/
theorem gaussianFieldFivePrimeMinus_under :
    (gaussianFieldFivePrimeMinus).under ℤ = Ideal.span {(5 : ℤ)} := by
  have hp5 : (Ideal.span {(5 : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by norm_num : (5 : ℤ) ≠ 0)]
    rw [Int.prime_iff_natAbs_prime]
    norm_num
  have hp5_ne : (Ideal.span {(5 : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    norm_num
  have h5conj : (5 : GaussianInt) ∈ Ideal.span {gaussianIntFiveConjugate} := by
    rw [Ideal.mem_span_singleton]
    exact ⟨gaussianIntFiveGenerator, by
      rw [mul_comm, gaussianIntFiveGenerator_mul_conjugate]⟩
  have h5mem : (5 : gaussianRingOfIntegers) ∈ gaussianFieldFivePrimeMinus := by
    rw [gaussianFieldFivePrimeMinus, Ideal.mem_comap]
    have hfive : gaussianRingOfIntegersEquivGaussianInt.toRingHom
        (5 : gaussianRingOfIntegers) = (5 : GaussianInt) := map_natCast _ 5
    rw [hfive]
    exact h5conj
  have hle : Ideal.span {(5 : ℤ)} ≤ (gaussianFieldFivePrimeMinus).under ℤ := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    change (5 : ℤ) ∈ Ideal.comap (algebraMap ℤ gaussianRingOfIntegers)
      gaussianFieldFivePrimeMinus
    rw [Ideal.mem_comap]
    simpa using h5mem
  have hne : (gaussianFieldFivePrimeMinus).under ℤ ≠ ⊤ := by
    intro h
    have h1 : (1 : ℤ) ∈ (gaussianFieldFivePrimeMinus).under ℤ := by
      rw [h]; exact Submodule.mem_top
    change (1 : ℤ) ∈ Ideal.comap (algebraMap ℤ gaussianRingOfIntegers)
      gaussianFieldFivePrimeMinus at h1
    rw [Ideal.mem_comap] at h1
    have hone : (1 : gaussianRingOfIntegers) ∈ gaussianFieldFivePrimeMinus := by
      simpa using h1
    have htop : (⊤ : Ideal gaussianRingOfIntegers) ≤ gaussianFieldFivePrimeMinus := by
      rw [top_le_iff, Ideal.eq_top_iff_one]
      exact hone
    exact gaussianFieldFivePrimeMinus_isMaximal.ne_top (top_le_iff.mp htop)
  exact (Ideal.IsMaximal.eq_of_le (hp5.isMaximal hp5_ne) hne hle).symm

instance gaussianFieldFivePrimePlus_liesOver :
    (gaussianFieldFivePrimePlus).LiesOver (Ideal.span {(5 : ℤ)}) :=
  ⟨gaussianFieldFivePrimePlus_under.symm⟩

instance gaussianFieldFivePrimeMinus_liesOver :
    (gaussianFieldFivePrimeMinus).LiesOver (Ideal.span {(5 : ℤ)}) :=
  ⟨gaussianFieldFivePrimeMinus_under.symm⟩

/-- Absolute norm of the transported plus prime is five. -/
theorem gaussianFieldFivePrimePlus_absNorm :
    (gaussianFieldFivePrimePlus).absNorm = 5 := by
  rw [Ideal.absNorm_apply]
  change Submodule.cardQuot gaussianFieldFivePrimePlus = 5
  rw [Submodule.cardQuot_apply]
  calc Nat.card (gaussianRingOfIntegers ⧸ gaussianFieldFivePrimePlus)
      = Nat.card (ZMod 5) :=
        Nat.card_congr gaussianFieldFivePrimePlusResidueEquiv.toEquiv
    _ = 5 := Nat.card_zmod 5

/-- Absolute norm of the principal ideal (5) in the ring of integers is 25. -/
theorem gaussianRingOfIntegers_five_absNorm :
    (Ideal.span {(5 : gaussianRingOfIntegers)}).absNorm = 25 := by
  change Ideal.absNorm (Ideal.span {((5 : ℕ) : gaussianRingOfIntegers)}) = 25
  rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, gaussianField_finrank]
  norm_num

/-- Absolute norm of the transported minus prime is five, from multiplicativity
of the ideal norm and the factorization (5) = plus * minus. -/
theorem gaussianFieldFivePrimeMinus_absNorm :
    (gaussianFieldFivePrimeMinus).absNorm = 5 := by
  have hfac := cardQuot_mul (I := gaussianFieldFivePrimePlus)
    (J := gaussianFieldFivePrimeMinus)
  rw [← gaussianFieldFive_ideal_factorization] at hfac
  have hprod : (Ideal.span {(5 : gaussianRingOfIntegers)}).absNorm =
      (gaussianFieldFivePrimePlus).absNorm *
        (gaussianFieldFivePrimeMinus).absNorm := by
    simpa [Ideal.absNorm_apply] using hfac
  rw [gaussianRingOfIntegers_five_absNorm, gaussianFieldFivePrimePlus_absNorm] at hprod
  omega

/-- The relative inertia degree at the plus prime is one. -/
theorem gaussianFieldFivePrimePlus_inertiaDeg :
    (Ideal.span {(5 : ℤ)}).inertiaDeg' gaussianFieldFivePrimePlus = 1 := by
  haveI := gaussianFieldFivePrimePlus_liesOver
  have hp : (Ideal.span {(5 : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by norm_num : (5 : ℤ) ≠ 0)]
    rw [Int.prime_iff_natAbs_prime]
    norm_num
  have hp_ne : (Ideal.span {(5 : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    norm_num
  have h := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver
    (P := gaussianFieldFivePrimePlus) (p := Ideal.span {(5 : ℤ)}) hp hp_ne
  rw [gaussianFieldFivePrimePlus_absNorm] at h
  have habs5 : (Ideal.absNorm (Ideal.span {(5 : ℤ)}) : ℕ) = 5 := by
    rw [Ideal.absNorm_span_singleton]
    norm_num
  rw [habs5] at h
  have hle1 : (Ideal.span {(5 : ℤ)}).inertiaDeg' gaussianFieldFivePrimePlus ≤ 1 := by
    by_contra hle
    have h2 : 2 ≤ (Ideal.span {(5 : ℤ)}).inertiaDeg' gaussianFieldFivePrimePlus := by omega
    have hmono : 5 ^ 2 ≤ 5 ^ ((Ideal.span {(5 : ℤ)}).inertiaDeg' gaussianFieldFivePrimePlus) :=
      Nat.pow_le_pow_right (by norm_num) h2
    rw [← h] at hmono
    norm_num at hmono
  have hpos : 1 ≤ (Ideal.span {(5 : ℤ)}).inertiaDeg' gaussianFieldFivePrimePlus := by
    by_contra h0
    have hzero : (Ideal.span {(5 : ℤ)}).inertiaDeg' gaussianFieldFivePrimePlus = 0 := by omega
    rw [hzero] at h
    norm_num at h
  omega


/-- The relative inertia degree at the minus prime is one. -/
theorem gaussianFieldFivePrimeMinus_inertiaDeg :
    (Ideal.span {(5 : ℤ)}).inertiaDeg' gaussianFieldFivePrimeMinus = 1 := by
  haveI := gaussianFieldFivePrimeMinus_liesOver
  have hp : (Ideal.span {(5 : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by norm_num : (5 : ℤ) ≠ 0)]
    rw [Int.prime_iff_natAbs_prime]
    norm_num
  have hp_ne : (Ideal.span {(5 : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    norm_num
  have h := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver
    (P := gaussianFieldFivePrimeMinus) (p := Ideal.span {(5 : ℤ)}) hp hp_ne
  rw [gaussianFieldFivePrimeMinus_absNorm] at h
  have habs5 : (Ideal.absNorm (Ideal.span {(5 : ℤ)}) : ℕ) = 5 := by
    rw [Ideal.absNorm_span_singleton]
    norm_num
  rw [habs5] at h
  have hle1 : (Ideal.span {(5 : ℤ)}).inertiaDeg' gaussianFieldFivePrimeMinus ≤ 1 := by
    by_contra hle
    have h2 : 2 ≤ (Ideal.span {(5 : ℤ)}).inertiaDeg' gaussianFieldFivePrimeMinus := by omega
    have hmono : 5 ^ 2 ≤ 5 ^ ((Ideal.span {(5 : ℤ)}).inertiaDeg' gaussianFieldFivePrimeMinus) :=
      Nat.pow_le_pow_right (by norm_num) h2
    rw [← h] at hmono
    norm_num at hmono
  have hpos : 1 ≤ (Ideal.span {(5 : ℤ)}).inertiaDeg' gaussianFieldFivePrimeMinus := by
    by_contra h0
    have hzero : (Ideal.span {(5 : ℤ)}).inertiaDeg' gaussianFieldFivePrimeMinus = 0 := by omega
    rw [hzero] at h
    norm_num at h
  omega


/-- The lifted plus prime does not contain the lifted minus prime. -/
theorem gaussianFieldFivePrimeMinus_not_le_plus :
    ¬ gaussianFieldFivePrimeMinus ≤ gaussianFieldFivePrimePlus := by
  intro hle
  exact gaussianFieldFivePrimePlus_ne_minus
    (gaussianFieldFivePrimeMinus_isMaximal.eq_of_le
      gaussianFieldFivePrimePlus_isMaximal.ne_top hle).symm

/-- The lifted plus prime contains the lifted minus prime. -/
theorem gaussianFieldFivePrimePlus_not_le_minus :
    ¬ gaussianFieldFivePrimePlus ≤ gaussianFieldFivePrimeMinus := by
  intro hle
  exact gaussianFieldFivePrimePlus_ne_minus
    (gaussianFieldFivePrimePlus_isMaximal.eq_of_le
      gaussianFieldFivePrimeMinus_isMaximal.ne_top hle)

/-- The ramification index at the plus prime is one (localization criterion). -/
theorem gaussianFieldFivePrimePlus_ramificationIdx :
    (Ideal.span {(5 : ℤ)}).ramificationIdx' gaussianFieldFivePrimePlus = 1 := by
  haveI hprime : gaussianFieldFivePrimePlus.IsPrime :=
    gaussianFieldFivePrimePlus_isMaximal.isPrime
  have hpne : gaussianFieldFivePrimePlus ≠ ⊥ := by
    have h5under : (5 : ℤ) ∈ gaussianFieldFivePrimePlus.under ℤ := by
      rw [gaussianFieldFivePrimePlus_under]
      exact Ideal.subset_span (by simp)
    have h5mem0 : algebraMap ℤ gaussianRingOfIntegers (5 : ℤ) ∈
        gaussianFieldFivePrimePlus := by
      change (5 : ℤ) ∈ Ideal.comap (algebraMap ℤ gaussianRingOfIntegers)
        gaussianFieldFivePrimePlus at h5under
      rwa [Ideal.mem_comap] at h5under
    have h5mem : (5 : gaussianRingOfIntegers) ∈ gaussianFieldFivePrimePlus := by
      simpa using h5mem0
    intro hbot
    have h5bot : (5 : gaussianRingOfIntegers) ∈ (⊥ : Ideal gaussianRingOfIntegers) :=
      hbot ▸ h5mem
    rw [Ideal.mem_bot] at h5bot
    exact (by norm_num : (5 : gaussianRingOfIntegers) ≠ 0) h5bot
  have hpP : (Ideal.span {(5 : ℤ)}).map
      (algebraMap ℤ gaussianRingOfIntegers) ≤ gaussianFieldFivePrimePlus := by
    rw [Ideal.map_le_iff_le_comap, ← Ideal.under_def, gaussianFieldFivePrimePlus_under]
  refine (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff
    (p := Ideal.span {(5 : ℤ)}) (P := gaussianFieldFivePrimePlus) hpne hpP).mpr ?_
  let T := Localization.AtPrime gaussianFieldFivePrimePlus
  have hmap : (Ideal.span {(5 : ℤ)}).map
      (algebraMap ℤ gaussianRingOfIntegers) =
      gaussianFieldFivePrimePlus * gaussianFieldFivePrimeMinus := by
    rw [Ideal.map_span]
    simp only [Set.image_singleton]
    have hfive : algebraMap ℤ gaussianRingOfIntegers (5 : ℤ) =
        (5 : gaussianRingOfIntegers) := map_natCast _ 5
    rw [hfive]
    exact gaussianFieldFive_ideal_factorization
  rw [IsScalarTower.algebraMap_eq ℤ gaussianRingOfIntegers T, ← Ideal.map_map, hmap,
    Ideal.map_mul, IsLocalization.AtPrime.map_eq_maximalIdeal
      (p := gaussianFieldFivePrimePlus) (Rₚ := T),
    IsLocalization.AtPrime.map_eq_top_of_not_le (S := T)
      (I := gaussianFieldFivePrimeMinus) (p := gaussianFieldFivePrimePlus)
      gaussianFieldFivePrimeMinus_not_le_plus]
  exact Ideal.mul_top _


/-- The ramification index at the minus prime is one (localization criterion). -/
theorem gaussianFieldFivePrimeMinus_ramificationIdx :
    (Ideal.span {(5 : ℤ)}).ramificationIdx' gaussianFieldFivePrimeMinus = 1 := by
  haveI hprime : gaussianFieldFivePrimeMinus.IsPrime :=
    gaussianFieldFivePrimeMinus_isMaximal.isPrime
  have hpne : gaussianFieldFivePrimeMinus ≠ ⊥ := by
    have h5under : (5 : ℤ) ∈ gaussianFieldFivePrimeMinus.under ℤ := by
      rw [gaussianFieldFivePrimeMinus_under]
      exact Ideal.subset_span (by simp)
    have h5mem0 : algebraMap ℤ gaussianRingOfIntegers (5 : ℤ) ∈
        gaussianFieldFivePrimeMinus := by
      change (5 : ℤ) ∈ Ideal.comap (algebraMap ℤ gaussianRingOfIntegers)
        gaussianFieldFivePrimeMinus at h5under
      rwa [Ideal.mem_comap] at h5under
    have h5mem : (5 : gaussianRingOfIntegers) ∈ gaussianFieldFivePrimeMinus := by
      simpa using h5mem0
    intro hbot
    have h5bot : (5 : gaussianRingOfIntegers) ∈ (⊥ : Ideal gaussianRingOfIntegers) :=
      hbot ▸ h5mem
    rw [Ideal.mem_bot] at h5bot
    exact (by norm_num : (5 : gaussianRingOfIntegers) ≠ 0) h5bot
  have hpP : (Ideal.span {(5 : ℤ)}).map
      (algebraMap ℤ gaussianRingOfIntegers) ≤ gaussianFieldFivePrimeMinus := by
    rw [Ideal.map_le_iff_le_comap, ← Ideal.under_def, gaussianFieldFivePrimeMinus_under]
  refine (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff
    (p := Ideal.span {(5 : ℤ)}) (P := gaussianFieldFivePrimeMinus) hpne hpP).mpr ?_
  let T := Localization.AtPrime gaussianFieldFivePrimeMinus
  have hmap : (Ideal.span {(5 : ℤ)}).map
      (algebraMap ℤ gaussianRingOfIntegers) =
      gaussianFieldFivePrimePlus * gaussianFieldFivePrimeMinus := by
    rw [Ideal.map_span]
    simp only [Set.image_singleton]
    have hfive : algebraMap ℤ gaussianRingOfIntegers (5 : ℤ) =
        (5 : gaussianRingOfIntegers) := map_natCast _ 5
    rw [hfive]
    exact gaussianFieldFive_ideal_factorization
  rw [IsScalarTower.algebraMap_eq ℤ gaussianRingOfIntegers T, ← Ideal.map_map, hmap,
    Ideal.map_mul,
    IsLocalization.AtPrime.map_eq_top_of_not_le (S := T)
      (I := gaussianFieldFivePrimePlus) (p := gaussianFieldFivePrimeMinus)
      gaussianFieldFivePrimePlus_not_le_minus,
    IsLocalization.AtPrime.map_eq_maximalIdeal
      (p := gaussianFieldFivePrimeMinus) (Rₚ := T)]
  exact Ideal.top_mul _



/-- The rational ring of integers. -/
abbrev gaussianRationalRingOfIntegers : Type := NumberField.RingOfIntegers ℚ

/-- The concrete height-one prime at 5 is the principal ideal generated by 5
in the rational ring of integers. -/
theorem concreteFiveHeightOne_asIdeal_eq_span :
    concreteFiveHeightOne.asIdeal =
      Ideal.span {(5 : gaussianRationalRingOfIntegers)} := by
  let e : gaussianRationalRingOfIntegers ≃+* ℤ :=
    Rat.IsIntegralClosure.intEquiv gaussianRationalRingOfIntegers
  have h := Rat.HeightOneSpectrum.span_natGenerator
    (R := gaussianRationalRingOfIntegers) concreteFiveHeightOne
  rw [concreteFiveHeightOne_natGenerator] at h
  change Ideal.span {(5 : ℤ)} =
    Ideal.map e.toRingHom concreteFiveHeightOne.asIdeal at h
  have h' := congrArg (Ideal.map e.symm.toRingHom) h
  rw [Ideal.map_span] at h'
  simp only [Set.image_singleton] at h'
  simp at h'
  exact h'.symm

/-- Maximality of the rational prime ideal (5). -/
theorem gaussianRationalFive_span_isMaximal :
    (Ideal.span {(5 : gaussianRationalRingOfIntegers)}).IsMaximal := by
  let e : gaussianRationalRingOfIntegers ≃+* ℤ :=
    Rat.IsIntegralClosure.intEquiv gaussianRationalRingOfIntegers
  have hpZ : (Ideal.span {(5 : ℤ)}).IsMaximal := by
    have hp5 : (Ideal.span {(5 : ℤ)}).IsPrime := by
      rw [Ideal.span_singleton_prime (by norm_num : (5 : ℤ) ≠ 0)]
      rw [Int.prime_iff_natAbs_prime]
      norm_num
    exact hp5.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; norm_num)
  have hmap : Ideal.map e.symm.toRingHom (Ideal.span {(5 : ℤ)}) =
      Ideal.span {(5 : gaussianRationalRingOfIntegers)} := by
    rw [Ideal.map_span]
    simp only [Set.image_singleton]
    congr 1
    simpa using map_natCast e.symm.toRingHom 5
  rw [← hmap]
  exact Ideal.map_isMaximal_of_equiv e.symm

/-- The lifted plus prime contains the rational integer 5. -/
theorem gaussianFieldFivePrimePlus_five_mem :
    (5 : gaussianRingOfIntegers) ∈ gaussianFieldFivePrimePlus := by
  rw [gaussianFieldFivePrimePlus, Ideal.mem_comap]
  have h5 : gaussianRingOfIntegersEquivGaussianInt.toRingHom
      (5 : gaussianRingOfIntegers) = (5 : GaussianInt) := map_natCast _ 5
  rw [h5]
  exact gaussianInt_five_mem_generator_ideal

/-- The lifted minus prime contains the rational integer 5. -/
theorem gaussianFieldFivePrimeMinus_five_mem :
    (5 : gaussianRingOfIntegers) ∈ gaussianFieldFivePrimeMinus := by
  rw [gaussianFieldFivePrimeMinus, Ideal.mem_comap]
  have h5 : gaussianRingOfIntegersEquivGaussianInt.toRingHom
      (5 : gaussianRingOfIntegers) = (5 : GaussianInt) := map_natCast _ 5
  rw [h5]
  rw [Ideal.mem_span_singleton]
  exact ⟨gaussianIntFiveGenerator, by
    rw [mul_comm, gaussianIntFiveGenerator_mul_conjugate]⟩

/-- The plus prime lies over the rational prime ideal (5). -/
theorem gaussianFieldFivePrimePlus_under_rational :
    (gaussianFieldFivePrimePlus).under gaussianRationalRingOfIntegers =
      Ideal.span {(5 : gaussianRationalRingOfIntegers)} := by
  haveI : gaussianFieldFivePrimePlus.IsPrime :=
    gaussianFieldFivePrimePlus_isMaximal.isPrime
  have hle : Ideal.span {(5 : gaussianRationalRingOfIntegers)} ≤
      (gaussianFieldFivePrimePlus).under gaussianRationalRingOfIntegers := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    change (5 : gaussianRationalRingOfIntegers) ∈
      Ideal.comap (algebraMap gaussianRationalRingOfIntegers gaussianRingOfIntegers)
        gaussianFieldFivePrimePlus
    rw [Ideal.mem_comap]
    have h5 : algebraMap gaussianRationalRingOfIntegers gaussianRingOfIntegers
        (5 : gaussianRationalRingOfIntegers) = (5 : gaussianRingOfIntegers) :=
      map_natCast _ 5
    rw [h5]
    exact gaussianFieldFivePrimePlus_five_mem
  have hne : (gaussianFieldFivePrimePlus).under gaussianRationalRingOfIntegers ≠ ⊤ := by
    intro h
    have h1 : (1 : gaussianRationalRingOfIntegers) ∈
        (gaussianFieldFivePrimePlus).under gaussianRationalRingOfIntegers := by
      rw [h]; exact Submodule.mem_top
    change (1 : gaussianRationalRingOfIntegers) ∈
      Ideal.comap (algebraMap gaussianRationalRingOfIntegers gaussianRingOfIntegers)
        gaussianFieldFivePrimePlus at h1
    rw [Ideal.mem_comap] at h1
    have hone : (1 : gaussianRingOfIntegers) ∈ gaussianFieldFivePrimePlus := by
      simpa using h1
    have htop : (⊤ : Ideal gaussianRingOfIntegers) ≤ gaussianFieldFivePrimePlus := by
      rw [top_le_iff, Ideal.eq_top_iff_one]
      exact hone
    exact gaussianFieldFivePrimePlus_isMaximal.ne_top (top_le_iff.mp htop)
  exact (Ideal.IsMaximal.eq_of_le gaussianRationalFive_span_isMaximal hne hle).symm

/-- The minus prime lies over the rational prime ideal (5). -/
theorem gaussianFieldFivePrimeMinus_under_rational :
    (gaussianFieldFivePrimeMinus).under gaussianRationalRingOfIntegers =
      Ideal.span {(5 : gaussianRationalRingOfIntegers)} := by
  haveI : gaussianFieldFivePrimeMinus.IsPrime :=
    gaussianFieldFivePrimeMinus_isMaximal.isPrime
  have hle : Ideal.span {(5 : gaussianRationalRingOfIntegers)} ≤
      (gaussianFieldFivePrimeMinus).under gaussianRationalRingOfIntegers := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    change (5 : gaussianRationalRingOfIntegers) ∈
      Ideal.comap (algebraMap gaussianRationalRingOfIntegers gaussianRingOfIntegers)
        gaussianFieldFivePrimeMinus
    rw [Ideal.mem_comap]
    have h5 : algebraMap gaussianRationalRingOfIntegers gaussianRingOfIntegers
        (5 : gaussianRationalRingOfIntegers) = (5 : gaussianRingOfIntegers) :=
      map_natCast _ 5
    rw [h5]
    exact gaussianFieldFivePrimeMinus_five_mem
  have hne : (gaussianFieldFivePrimeMinus).under gaussianRationalRingOfIntegers ≠ ⊤ := by
    intro h
    have h1 : (1 : gaussianRationalRingOfIntegers) ∈
        (gaussianFieldFivePrimeMinus).under gaussianRationalRingOfIntegers := by
      rw [h]; exact Submodule.mem_top
    change (1 : gaussianRationalRingOfIntegers) ∈
      Ideal.comap (algebraMap gaussianRationalRingOfIntegers gaussianRingOfIntegers)
        gaussianFieldFivePrimeMinus at h1
    rw [Ideal.mem_comap] at h1
    have hone : (1 : gaussianRingOfIntegers) ∈ gaussianFieldFivePrimeMinus := by
      simpa using h1
    have htop : (⊤ : Ideal gaussianRingOfIntegers) ≤ gaussianFieldFivePrimeMinus := by
      rw [top_le_iff, Ideal.eq_top_iff_one]
      exact hone
    exact gaussianFieldFivePrimeMinus_isMaximal.ne_top (top_le_iff.mp htop)
  exact (Ideal.IsMaximal.eq_of_le gaussianRationalFive_span_isMaximal hne hle).symm

instance gaussianFieldFivePrimePlus_liesOver_rational :
    (gaussianFieldFivePrimePlus).LiesOver
      (Ideal.span {(5 : gaussianRationalRingOfIntegers)}) :=
  ⟨gaussianFieldFivePrimePlus_under_rational.symm⟩

instance gaussianFieldFivePrimeMinus_liesOver_rational :
    (gaussianFieldFivePrimeMinus).LiesOver
      (Ideal.span {(5 : gaussianRationalRingOfIntegers)}) :=
  ⟨gaussianFieldFivePrimeMinus_under_rational.symm⟩

/-- Absolute norm of (5) in the rational ring of integers is 5. -/
theorem gaussianRationalFive_absNorm :
    (Ideal.span {(5 : gaussianRationalRingOfIntegers)}).absNorm = 5 := by
  change Ideal.absNorm (Ideal.span {((5 : ℕ) : gaussianRationalRingOfIntegers)}) = 5
  rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, Module.finrank_self]
  norm_num


/-- Scalar tower Z -> O_Q -> O(GaussianField). -/
instance gaussianRingOfIntegers_scalarTower_rational :
    IsScalarTower ℤ gaussianRationalRingOfIntegers gaussianRingOfIntegers :=
  IsScalarTower.of_algebraMap_eq fun x => by
    have h : (algebraMap gaussianRationalRingOfIntegers gaussianRingOfIntegers).comp
        (algebraMap ℤ gaussianRationalRingOfIntegers) =
        algebraMap ℤ gaussianRingOfIntegers := RingHom.ext_int _ _
    exact (congrArg (fun f : ℤ →+* gaussianRingOfIntegers => f x) h).symm

/-- Finiteness of O(GaussianField) over O_Q, by restricting the Z-finiteness. -/
instance gaussianRingOfIntegers_finite_rational :
    Module.Finite gaussianRationalRingOfIntegers gaussianRingOfIntegers :=
  Module.Finite.of_restrictScalars_finite ℤ
    gaussianRationalRingOfIntegers gaussianRingOfIntegers

/-- The inertia degree at plus over the rational prime (5) is one. -/
theorem gaussianFieldFivePrimePlus_inertiaDeg_rational :
    (Ideal.span {(5 : gaussianRationalRingOfIntegers)}).inertiaDeg'
      gaussianFieldFivePrimePlus = 1 := by
  haveI := gaussianFieldFivePrimePlus_liesOver_rational
  have hpR_prime : (Ideal.span {(5 : gaussianRationalRingOfIntegers)}).IsPrime :=
    gaussianRationalFive_span_isMaximal.isPrime
  have hpR_ne : (Ideal.span {(5 : gaussianRationalRingOfIntegers)}) ≠ ⊥ := by
    intro h
    have h5 : (5 : gaussianRationalRingOfIntegers) ∈
        (⊥ : Ideal gaussianRationalRingOfIntegers) :=
      h ▸ Ideal.mem_span_singleton_self (5 : gaussianRationalRingOfIntegers)
    rw [Ideal.mem_bot] at h5
    exact (by norm_num : (5 : gaussianRationalRingOfIntegers) ≠ 0) h5
  have h := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver
    (P := gaussianFieldFivePrimePlus)
    (p := Ideal.span {(5 : gaussianRationalRingOfIntegers)}) hpR_prime hpR_ne
  rw [gaussianFieldFivePrimePlus_absNorm, gaussianRationalFive_absNorm] at h
  have hle1 : (Ideal.span {(5 : gaussianRationalRingOfIntegers)}).inertiaDeg'
      gaussianFieldFivePrimePlus ≤ 1 := by
    by_contra hle
    have h2 : 2 ≤ (Ideal.span {(5 : gaussianRationalRingOfIntegers)}).inertiaDeg'
        gaussianFieldFivePrimePlus := by omega
    have hmono : 5 ^ 2 ≤ 5 ^ ((Ideal.span {(5 : gaussianRationalRingOfIntegers)}).inertiaDeg'
        gaussianFieldFivePrimePlus) := Nat.pow_le_pow_right (by norm_num) h2
    rw [← h] at hmono
    norm_num at hmono
  have hpos : 1 ≤ (Ideal.span {(5 : gaussianRationalRingOfIntegers)}).inertiaDeg'
      gaussianFieldFivePrimePlus := by
    by_contra h0
    have hzero : (Ideal.span {(5 : gaussianRationalRingOfIntegers)}).inertiaDeg'
        gaussianFieldFivePrimePlus = 0 := by omega
    rw [hzero] at h
    norm_num at h
  omega

/-- The inertia degree at minus over the rational prime (5) is one. -/
theorem gaussianFieldFivePrimeMinus_inertiaDeg_rational :
    (Ideal.span {(5 : gaussianRationalRingOfIntegers)}).inertiaDeg'
      gaussianFieldFivePrimeMinus = 1 := by
  haveI := gaussianFieldFivePrimeMinus_liesOver_rational
  have hpR_prime : (Ideal.span {(5 : gaussianRationalRingOfIntegers)}).IsPrime :=
    gaussianRationalFive_span_isMaximal.isPrime
  have hpR_ne : (Ideal.span {(5 : gaussianRationalRingOfIntegers)}) ≠ ⊥ := by
    intro h
    have h5 : (5 : gaussianRationalRingOfIntegers) ∈
        (⊥ : Ideal gaussianRationalRingOfIntegers) :=
      h ▸ Ideal.mem_span_singleton_self (5 : gaussianRationalRingOfIntegers)
    rw [Ideal.mem_bot] at h5
    exact (by norm_num : (5 : gaussianRationalRingOfIntegers) ≠ 0) h5
  have h := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver
    (P := gaussianFieldFivePrimeMinus)
    (p := Ideal.span {(5 : gaussianRationalRingOfIntegers)}) hpR_prime hpR_ne
  rw [gaussianFieldFivePrimeMinus_absNorm, gaussianRationalFive_absNorm] at h
  have hle1 : (Ideal.span {(5 : gaussianRationalRingOfIntegers)}).inertiaDeg'
      gaussianFieldFivePrimeMinus ≤ 1 := by
    by_contra hle
    have h2 : 2 ≤ (Ideal.span {(5 : gaussianRationalRingOfIntegers)}).inertiaDeg'
        gaussianFieldFivePrimeMinus := by omega
    have hmono : 5 ^ 2 ≤ 5 ^ ((Ideal.span {(5 : gaussianRationalRingOfIntegers)}).inertiaDeg'
        gaussianFieldFivePrimeMinus) := Nat.pow_le_pow_right (by norm_num) h2
    rw [← h] at hmono
    norm_num at hmono
  have hpos : 1 ≤ (Ideal.span {(5 : gaussianRationalRingOfIntegers)}).inertiaDeg'
      gaussianFieldFivePrimeMinus := by
    by_contra h0
    have hzero : (Ideal.span {(5 : gaussianRationalRingOfIntegers)}).inertiaDeg'
        gaussianFieldFivePrimeMinus = 0 := by omega
    rw [hzero] at h
    norm_num at h
  omega


/-- The ramification index at plus over the rational prime (5) is one. -/
theorem gaussianFieldFivePrimePlus_ramificationIdx_rational :
    (Ideal.span {(5 : gaussianRationalRingOfIntegers)}).ramificationIdx'
      gaussianFieldFivePrimePlus = 1 := by
  haveI hprime : gaussianFieldFivePrimePlus.IsPrime :=
    gaussianFieldFivePrimePlus_isMaximal.isPrime
  have hpne : gaussianFieldFivePrimePlus ≠ ⊥ := by
    intro h
    have h5bot : (5 : gaussianRingOfIntegers) ∈
        (⊥ : Ideal gaussianRingOfIntegers) :=
      h ▸ gaussianFieldFivePrimePlus_five_mem
    rw [Ideal.mem_bot] at h5bot
    exact (by norm_num : (5 : gaussianRingOfIntegers) ≠ 0) h5bot
  have hmapR : (Ideal.span {(5 : gaussianRationalRingOfIntegers)}).map
      (algebraMap gaussianRationalRingOfIntegers gaussianRingOfIntegers) =
      Ideal.span {(5 : gaussianRingOfIntegers)} := by
    rw [Ideal.map_span]
    simp only [Set.image_singleton]
    have h5 : algebraMap gaussianRationalRingOfIntegers gaussianRingOfIntegers
        (5 : gaussianRationalRingOfIntegers) = (5 : gaussianRingOfIntegers) :=
      map_natCast _ 5
    rw [h5]
  have hpP : (Ideal.span {(5 : gaussianRationalRingOfIntegers)}).map
      (algebraMap gaussianRationalRingOfIntegers gaussianRingOfIntegers) ≤
      gaussianFieldFivePrimePlus := by
    rw [hmapR, gaussianFieldFive_ideal_factorization]
    exact Ideal.mul_le_right
  refine (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff
    (p := Ideal.span {(5 : gaussianRationalRingOfIntegers)})
    (P := gaussianFieldFivePrimePlus) hpne hpP).mpr ?_
  let T := Localization.AtPrime gaussianFieldFivePrimePlus
  haveI : IsScalarTower gaussianRationalRingOfIntegers
      gaussianRingOfIntegers T :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  rw [IsScalarTower.algebraMap_eq gaussianRationalRingOfIntegers
      gaussianRingOfIntegers T, ← Ideal.map_map, hmapR,
    gaussianFieldFive_ideal_factorization, Ideal.map_mul,
    IsLocalization.AtPrime.map_eq_maximalIdeal
      (p := gaussianFieldFivePrimePlus) (Rₚ := T),
    IsLocalization.AtPrime.map_eq_top_of_not_le (S := T)
      (I := gaussianFieldFivePrimeMinus) (p := gaussianFieldFivePrimePlus)
      gaussianFieldFivePrimeMinus_not_le_plus]
  exact Ideal.mul_top _

/-- The ramification index at minus over the rational prime (5) is one. -/
theorem gaussianFieldFivePrimeMinus_ramificationIdx_rational :
    (Ideal.span {(5 : gaussianRationalRingOfIntegers)}).ramificationIdx'
      gaussianFieldFivePrimeMinus = 1 := by
  haveI hprime : gaussianFieldFivePrimeMinus.IsPrime :=
    gaussianFieldFivePrimeMinus_isMaximal.isPrime
  have hpne : gaussianFieldFivePrimeMinus ≠ ⊥ := by
    intro h
    have h5bot : (5 : gaussianRingOfIntegers) ∈
        (⊥ : Ideal gaussianRingOfIntegers) :=
      h ▸ gaussianFieldFivePrimeMinus_five_mem
    rw [Ideal.mem_bot] at h5bot
    exact (by norm_num : (5 : gaussianRingOfIntegers) ≠ 0) h5bot
  have hmapR : (Ideal.span {(5 : gaussianRationalRingOfIntegers)}).map
      (algebraMap gaussianRationalRingOfIntegers gaussianRingOfIntegers) =
      Ideal.span {(5 : gaussianRingOfIntegers)} := by
    rw [Ideal.map_span]
    simp only [Set.image_singleton]
    have h5 : algebraMap gaussianRationalRingOfIntegers gaussianRingOfIntegers
        (5 : gaussianRationalRingOfIntegers) = (5 : gaussianRingOfIntegers) :=
      map_natCast _ 5
    rw [h5]
  have hpP : (Ideal.span {(5 : gaussianRationalRingOfIntegers)}).map
      (algebraMap gaussianRationalRingOfIntegers gaussianRingOfIntegers) ≤
      gaussianFieldFivePrimeMinus := by
    rw [hmapR, gaussianFieldFive_ideal_factorization]
    exact Ideal.mul_le_left
  refine (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff
    (p := Ideal.span {(5 : gaussianRationalRingOfIntegers)})
    (P := gaussianFieldFivePrimeMinus) hpne hpP).mpr ?_
  let T := Localization.AtPrime gaussianFieldFivePrimeMinus
  haveI : IsScalarTower gaussianRationalRingOfIntegers
      gaussianRingOfIntegers T :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  rw [IsScalarTower.algebraMap_eq gaussianRationalRingOfIntegers
      gaussianRingOfIntegers T, ← Ideal.map_map, hmapR,
    gaussianFieldFive_ideal_factorization, Ideal.map_mul,
    IsLocalization.AtPrime.map_eq_top_of_not_le (S := T)
      (I := gaussianFieldFivePrimePlus) (p := gaussianFieldFivePrimeMinus)
      gaussianFieldFivePrimePlus_not_le_minus,
    IsLocalization.AtPrime.map_eq_maximalIdeal
      (p := gaussianFieldFivePrimeMinus) (Rₚ := T)]
  exact Ideal.top_mul _

/-- Relative ramification index of the concrete Gaussian place is one. -/
theorem concreteGaussianFivePlace_relativeRamificationIndex_eq_one :
    LeanFormal.IUT.NumberFieldFinitePlace.relativeRamificationIndex
      (k := ℚ) concreteGaussianFivePlace = 1 := by
  rcases concreteGaussianFivePlace_maximalIdeal_eq_plus_or_minus with h | h
  · rw [LeanFormal.IUT.NumberFieldFinitePlace.relativeRamificationIndex]
    rw [concreteGaussianFivePlace_comap, concreteFivePlace_maximalIdeal,
      concreteFiveHeightOne_asIdeal_eq_span, h]
    exact gaussianFieldFivePrimePlus_ramificationIdx_rational
  · rw [LeanFormal.IUT.NumberFieldFinitePlace.relativeRamificationIndex]
    rw [concreteGaussianFivePlace_comap, concreteFivePlace_maximalIdeal,
      concreteFiveHeightOne_asIdeal_eq_span, h]
    exact gaussianFieldFivePrimeMinus_ramificationIdx_rational

/-- Relative residue degree of the concrete Gaussian place is one. -/
theorem concreteGaussianFivePlace_relativeResidueDegree_eq_one :
    LeanFormal.IUT.NumberFieldFinitePlace.relativeResidueDegree
      (k := ℚ) concreteGaussianFivePlace = 1 := by
  rcases concreteGaussianFivePlace_maximalIdeal_eq_plus_or_minus with h | h
  · rw [LeanFormal.IUT.NumberFieldFinitePlace.relativeResidueDegree]
    rw [concreteGaussianFivePlace_comap, concreteFivePlace_maximalIdeal,
      concreteFiveHeightOne_asIdeal_eq_span, h]
    exact gaussianFieldFivePrimePlus_inertiaDeg_rational
  · rw [LeanFormal.IUT.NumberFieldFinitePlace.relativeResidueDegree]
    rw [concreteGaussianFivePlace_comap, concreteFivePlace_maximalIdeal,
      concreteFiveHeightOne_asIdeal_eq_span, h]
    exact gaussianFieldFivePrimeMinus_inertiaDeg_rational

/-- Relative completion degree e*f of the concrete Gaussian place is one. -/
theorem concreteGaussianFivePlace_relativeCompletionDegree_eq_one :
    LeanFormal.IUT.NumberFieldFinitePlace.relativeCompletionDegree
      (k := ℚ) concreteGaussianFivePlace = 1 := by
  rw [LeanFormal.IUT.NumberFieldFinitePlace.relativeCompletionDegree,
    concreteGaussianFivePlace_relativeRamificationIndex_eq_one,
    concreteGaussianFivePlace_relativeResidueDegree_eq_one, mul_one]

/-- M4: the completed valuation rings at the concrete place form a finite module
extension (the tree's unconditional gap-A theorem, instantiated). -/
theorem concreteGaussianFivePlace_moduleFinite_completionIntegers :
    Module.Finite
      ((NumberFieldFinitePlace.comap (k := ℚ) concreteGaussianFivePlace).maximalIdeal.adicCompletionIntegers ℚ)
      (concreteGaussianFivePlace.maximalIdeal.adicCompletionIntegers GaussianField) :=
  LeanFormal.IUT.NumberFieldFinitePlace.moduleFinite_adicCompletionIntegers
    (k := ℚ) concreteGaussianFivePlace

/-- The local completion degree of the concrete Gaussian place over Q_5 is one. -/
theorem concreteGaussianFivePlace_completion_finrank_eq_one :
    Module.finrank
      ((NumberFieldFinitePlace.comap (k := ℚ) concreteGaussianFivePlace).maximalIdeal.adicCompletion ℚ)
      (concreteGaussianFivePlace.maximalIdeal.adicCompletion GaussianField) = 1 := by
  rw [LeanFormal.IUT.NumberFieldFinitePlace.finrank_adicCompletion_eq_relativeCompletionDegree_of_moduleFinite
        (k := ℚ) concreteGaussianFivePlace
        concreteGaussianFivePlace_moduleFinite_completionIntegers,
    concreteGaussianFivePlace_relativeCompletionDegree_eq_one]

/-! ## Residue field and valuation of the chosen Gaussian place over 5

The two primes over 5 are computed explicitly above.  The chosen place
`concreteGaussianFivePlace` is produced from Mathlib's lying-over surjectivity,
so the construction does not determine which of the two primes it is; both
possibilities are kept as a disjunction.  The statements below are therefore
uniform in the prime: every prime of Z[i] over 5 has residue ring `ZMod 5`, and
the chosen place inherits the residue field, its characteristic, and the
normalization `e = 1` of the valuation. -/

/-- Every prime of the ring of integers of the Gaussian field that contains 5
has residue ring ZMod 5, in the sense that the quotient is nonempty as a ring
equivalent to ZMod 5. -/
theorem gaussianFieldFiveResidueEquivOfMemFive_nonempty
    (P : Ideal gaussianRingOfIntegers) [hP : P.IsPrime]
    (h5 : (5 : gaussianRingOfIntegers) ∈ P) :
    Nonempty ((gaussianRingOfIntegers ⧸ P) ≃+* ZMod 5) := by
  rcases gaussianFieldFivePrime_classification P
      (Ideal.span_le.mpr (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact h5)) with h | h
  · exact ⟨h.symm ▸ gaussianFieldFivePrimePlusResidueEquiv⟩
  · exact ⟨h.symm ▸ gaussianFieldFivePrimeMinusResidueEquiv⟩

/-- Every prime of the ring of integers of the Gaussian field that contains 5
has residue ring ZMod 5. -/
noncomputable def gaussianFieldFiveResidueEquivOfMemFive
    (P : Ideal gaussianRingOfIntegers) [hP : P.IsPrime]
    (h5 : (5 : gaussianRingOfIntegers) ∈ P) :
    (gaussianRingOfIntegers ⧸ P) ≃+* ZMod 5 :=
  Classical.choice (gaussianFieldFiveResidueEquivOfMemFive_nonempty P h5)

/-- The residue field of the chosen Gaussian place over 5 is ZMod 5. -/
noncomputable def concreteGaussianFivePlaceResidueEquiv :
    NumberFieldFinitePlace.ResidueField concreteGaussianFivePlace ≃+* ZMod 5 :=
  letI : (concreteGaussianFivePlace.maximalIdeal : Ideal gaussianRingOfIntegers).IsPrime :=
    concreteGaussianFivePlace.maximalIdeal.isPrime
  gaussianFieldFiveResidueEquivOfMemFive
    (P := (concreteGaussianFivePlace.maximalIdeal : Ideal gaussianRingOfIntegers))
    concreteGaussianFivePlace_five_mem

/-- The residue field of the chosen Gaussian place has five elements. -/
theorem concreteGaussianFivePlaceResidueField_card :
    Nat.card (NumberFieldFinitePlace.ResidueField concreteGaussianFivePlace) = 5 := by
  rw [Nat.card_congr concreteGaussianFivePlaceResidueEquiv.toEquiv, Nat.card_zmod]

/-- The residue field of the completion at the chosen Gaussian place is ZMod 5,
obtained by transporting the residue field along the completed valuation ring. -/
noncomputable def concreteGaussianFivePlaceCompletionResidueEquiv :
    IsLocalRing.ResidueField
        (concreteGaussianFivePlace.maximalIdeal.adicCompletionIntegers GaussianField) ≃+* ZMod 5 :=
  (NumberFieldFinitePlace.residueEquivAdicCompletionIntegers
    concreteGaussianFivePlace).symm.trans concreteGaussianFivePlaceResidueEquiv

/-- The residue field of the completion at the chosen Gaussian place has five
elements. -/
theorem concreteGaussianFivePlaceCompletionResidueField_card :
    Nat.card (IsLocalRing.ResidueField
      (concreteGaussianFivePlace.maximalIdeal.adicCompletionIntegers GaussianField)) = 5 := by
  rw [Nat.card_congr concreteGaussianFivePlaceCompletionResidueEquiv.toEquiv, Nat.card_zmod]

/-- The chosen Gaussian place over 5 lies over the rational prime ideal (5). -/
theorem concreteGaussianFivePlace_under_rational :
    (concreteGaussianFivePlace.maximalIdeal : Ideal gaussianRingOfIntegers).under
        gaussianRationalRingOfIntegers =
      Ideal.span {(5 : gaussianRationalRingOfIntegers)} := by
  rw [concreteGaussianFivePlace_under_eq, concreteFiveHeightOne_asIdeal_eq_span]

/-- The residue characteristic of the chosen Gaussian place is 5. -/
theorem concreteGaussianFivePlace_residueCharacteristic :
    NumberFieldFinitePlace.residueCharacteristic concreteGaussianFivePlace = 5 := by
  rw [NumberFieldFinitePlace.residueCharacteristic]
  change ringChar (gaussianRingOfIntegers ⧸
    (concreteGaussianFivePlace.maximalIdeal : Ideal gaussianRingOfIntegers)) = 5
  rw [Ideal.ringChar_quot]
  have habs : Ideal.absNorm (Ideal.span {(5 : ℤ)}) = 5 := by
    rw [Ideal.absNorm_span_singleton]
    rw [show (5 : ℤ) = algebraMap ℤ ℤ 5 by simp, Algebra.norm_algebraMap,
      Module.finrank_self]
    norm_num
  rcases concreteGaussianFivePlace_maximalIdeal_eq_plus_or_minus with h | h
  · rw [h, gaussianFieldFivePrimePlus_under, habs]
  · rw [h, gaussianFieldFivePrimeMinus_under, habs]

/-- The ramification index of the chosen Gaussian place over the rational prime
5, in the classical `ramificationIdx'` form used by the valuation identity. -/
theorem concreteGaussianFivePlace_ramificationIdx_eq_one :
    Ideal.ramificationIdx'
        (NumberFieldFinitePlace.comap (k := ℚ) concreteGaussianFivePlace).maximalIdeal.asIdeal
        concreteGaussianFivePlace.maximalIdeal.asIdeal = 1 :=
  concreteGaussianFivePlace_relativeRamificationIndex_eq_one

/-- Valuation compatibility at the chosen place: for a rational number `x`, the
valuation of `x` at the chosen Gaussian place equals the 5-adic valuation of
`x`.  This is the normalization `e = 1` of the relative ramification index. -/
theorem concreteGaussianFivePlace_valuation_algebraMap (x : ℚ) :
    (IsDedekindDomain.HeightOneSpectrum.valuation ℚ
        (NumberFieldFinitePlace.comap (k := ℚ) concreteGaussianFivePlace).maximalIdeal) x =
      (IsDedekindDomain.HeightOneSpectrum.valuation GaussianField
        concreteGaussianFivePlace.maximalIdeal) (algebraMap ℚ GaussianField x) := by
  have h := NumberFieldFinitePlace.valuation_algebraMap (k := ℚ)
    concreteGaussianFivePlace x
  rwa [concreteGaussianFivePlace_ramificationIdx_eq_one, pow_one] at h

/-- Unit-level form of the valuation compatibility: a rational number is a unit
of the 5-adic valuation ring if and only if its image is a unit of the Gaussian
place valuation ring. -/
theorem concreteGaussianFivePlace_valuation_eq_one_iff (x : ℚ) :
    (IsDedekindDomain.HeightOneSpectrum.valuation ℚ
        (NumberFieldFinitePlace.comap (k := ℚ) concreteGaussianFivePlace).maximalIdeal) x = 1 ↔
      (IsDedekindDomain.HeightOneSpectrum.valuation GaussianField
        concreteGaussianFivePlace.maximalIdeal) (algebraMap ℚ GaussianField x) = 1 := by
  rw [concreteGaussianFivePlace_valuation_algebraMap]

/-- Valuation compatibility after completing at the chosen place: the value of
a 5-adic number equals the value of its image in the Gaussian completion. -/
theorem concreteGaussianFivePlace_valuation_completionMap
    (x : IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      (NumberFieldFinitePlace.comap (k := ℚ) concreteGaussianFivePlace).maximalIdeal) :
    Valued.v x =
      Valued.v (NumberFieldFinitePlace.completionMap concreteGaussianFivePlace x) := by
  have h := NumberFieldFinitePlace.valuation_completionMap (k := ℚ)
    concreteGaussianFivePlace x
  rwa [concreteGaussianFivePlace_ramificationIdx_eq_one, pow_one] at h

end LeanFormal.IUT.IUTII.Frobenioid.Example36
