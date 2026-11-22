import tmp.sheaf.xif.paper.S2702SplitAnyPlaceActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
import LeanFormal.IUT.Foundations.NumberField.PlaceCompletionCarrier
import Mathlib.Tactic

/-!
# S2703: the Gaussian prime places at 5 and 2161

This file constructs, from the actual Gaussian integers and the actual
ring-of-integers equivalence

* the two Gaussian primes 44 + 15i and 44 - 15i above the rational prime
  2161 = 44^2 + 15^2, with their norm computation and primality;
* the four finite places of the Gaussian field above 5 and 2161, obtained
  from the maximal ideals (2+i), (2-i), (44+15i), (44-15i) transported
  to the ring of integers;
* the residue characteristics (5 and 2161) and oddness of these places;
* split multiplicative reduction of the concrete split curve over each of the
  four places, using the two rational split theorems of S2702;
* the valuation bridge: a number-ring element in the maximal ideal of a finite
  place has value < 1 in the completed valuation.

The IsPrime statement for (44+15i) is proved through irreducibility from
the norm, not through Ideal.prime_of_irreducible_absNorm_span; this avoids the
known Algebra.norm/Zsqrtd.norm defeq gap.  The absolute norm identity is
recovered separately from the explicit residue quotient.
-/

noncomputable section

open Polynomial
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S2696VbadActual
open LeanFormal.IUT.XiFPaper.S2702SplitAnyPlaceActual

namespace LeanFormal.IUT.XiFPaper.S2703GaussianPrimePlacesActual

set_option maxHeartbeats 4000000

local instance s2703GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- The Gaussian ring of integers. -/
abbrev gaussianO : Type := NumberField.RingOfIntegers GaussianField

/-- The rational ring of integers. -/
abbrev rationalO : Type := NumberField.RingOfIntegers ℚ

/-! ## 1. The Gaussian primes 44 ± 15i over 2161 -/

/-- The Gaussian integer 44 + 15i. -/
def piPlus : GaussianInt := ⟨44, 15⟩

/-- The conjugate Gaussian integer 44 - 15i. -/
def piMinus : GaussianInt := ⟨44, -15⟩

/-- The norm of 44 + 15i is the rational prime 2161. -/
theorem piPlus_norm : Zsqrtd.norm piPlus = 2161 := by
  simp [piPlus, Zsqrtd.norm_def]

/-- The norm of 44 - 15i is the rational prime 2161. -/
theorem piMinus_norm : Zsqrtd.norm piMinus = 2161 := by
  simp [piMinus, Zsqrtd.norm_def]

/-- The factorization (44+15i)(44-15i) = 2161 in the Gaussian integers. -/
theorem piPlus_mul_piMinus : piPlus * piMinus = (2161 : GaussianInt) := by
  apply Zsqrtd.ext_iff.mpr
  constructor <;> norm_num [piPlus, piMinus]

/-- 2161 is prime. -/
theorem natPrime2161 : Nat.Prime 2161 := by
  norm_num

local instance s2703Fact2161 : Fact (Nat.Prime 2161) := ⟨natPrime2161⟩

/-- 44 + 15i is irreducible: its norm is prime. -/
theorem piPlus_irreducible : Irreducible piPlus := by
  rw [irreducible_iff]
  constructor
  · intro hunit
    have hnorm : (Zsqrtd.norm piPlus).natAbs = 1 :=
      Zsqrtd.norm_eq_one_iff.mpr hunit
    rw [piPlus_norm] at hnorm
    norm_num at hnorm
  · intro a b hab
    have hnorm : (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs = 2161 := by
      calc (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs
          = (Zsqrtd.norm (a * b)).natAbs := by rw [Zsqrtd.norm_mul, Int.natAbs_mul]
        _ = (Zsqrtd.norm piPlus).natAbs := by rw [hab]
        _ = 2161 := by rw [piPlus_norm]; norm_num
    have hdvd : (Zsqrtd.norm a).natAbs ∣ 2161 := ⟨(Zsqrtd.norm b).natAbs, hnorm.symm⟩
    have hcases := natPrime2161.eq_one_or_self_of_dvd ((Zsqrtd.norm a).natAbs) hdvd
    rcases hcases with ha | ha
    · left
      exact Zsqrtd.norm_eq_one_iff.mp ha
    · right
      have hb : (Zsqrtd.norm b).natAbs = 1 := by
        rw [ha] at hnorm
        omega
      exact Zsqrtd.norm_eq_one_iff.mp hb

/-- The conjugate 44 - 15i is irreducible: its norm is prime. -/
theorem piMinus_irreducible : Irreducible piMinus := by
  rw [irreducible_iff]
  constructor
  · intro hunit
    have hnorm : (Zsqrtd.norm piMinus).natAbs = 1 :=
      Zsqrtd.norm_eq_one_iff.mpr hunit
    rw [piMinus_norm] at hnorm
    norm_num at hnorm
  · intro a b hab
    have hnorm : (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs = 2161 := by
      calc (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs
          = (Zsqrtd.norm (a * b)).natAbs := by rw [Zsqrtd.norm_mul, Int.natAbs_mul]
        _ = (Zsqrtd.norm piMinus).natAbs := by rw [hab]
        _ = 2161 := by rw [piMinus_norm]; norm_num
    have hdvd : (Zsqrtd.norm a).natAbs ∣ 2161 := ⟨(Zsqrtd.norm b).natAbs, hnorm.symm⟩
    have hcases := natPrime2161.eq_one_or_self_of_dvd ((Zsqrtd.norm a).natAbs) hdvd
    rcases hcases with ha | ha
    · left
      exact Zsqrtd.norm_eq_one_iff.mp ha
    · right
      have hb : (Zsqrtd.norm b).natAbs = 1 := by
        rw [ha] at hnorm
        omega
      exact Zsqrtd.norm_eq_one_iff.mp hb

/-- The principal ideal (44+15i) is maximal. -/
theorem piPlus_ideal_isMaximal : (Ideal.span {piPlus}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible piPlus_irreducible

/-- The principal ideal (44+15i) is prime. -/
theorem piPlus_ideal_isPrime : (Ideal.span {piPlus}).IsPrime :=
  piPlus_ideal_isMaximal.isPrime

/-- The principal ideal (44-15i) is maximal. -/
theorem piMinus_ideal_isMaximal : (Ideal.span {piMinus}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible piMinus_irreducible

/-- The principal ideal (44-15i) is prime. -/
theorem piMinus_ideal_isPrime : (Ideal.span {piMinus}).IsPrime :=
  piMinus_ideal_isMaximal.isPrime

instance piPlus_ideal_isMaximal_instance : (Ideal.span {piPlus}).IsMaximal :=
  piPlus_ideal_isMaximal

instance piMinus_ideal_isMaximal_instance : (Ideal.span {piMinus}).IsMaximal :=
  piMinus_ideal_isMaximal

/-! ## 2. The residue quotients at 2161 -/

/-- The residue map Z[i] -> ZMod 2161 at 44+15i, sending i to
2014 = -147, where 147^2 = -1 (mod 2161). -/
noncomputable def gaussianInt2161PlusResidueMap : GaussianInt →+* ZMod 2161 :=
  Zsqrtd.lift ⟨(2014 : ZMod 2161), by decide⟩

/-- The residue map at 44+15i kills the generator. -/
theorem gaussianInt2161PlusResidueMap_generator :
    gaussianInt2161PlusResidueMap piPlus = 0 := by
  simp [gaussianInt2161PlusResidueMap, piPlus]
  decide

/-- The residue map at 44+15i is surjective already on integer classes. -/
theorem gaussianInt2161PlusResidueMap_surjective :
    Function.Surjective gaussianInt2161PlusResidueMap := by
  intro y
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective y
  refine ⟨(a : GaussianInt), ?_⟩
  simp [gaussianInt2161PlusResidueMap]

/-- The ideal (44+15i) is contained in the kernel of the residue map. -/
theorem gaussianInt2161Plus_ideal_le_ker :
    Ideal.span {piPlus} ≤ RingHom.ker gaussianInt2161PlusResidueMap := by
  refine Ideal.span_le.mpr ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact (RingHom.mem_ker).mpr gaussianInt2161PlusResidueMap_generator

/-- The kernel of the residue map at 44+15i is exactly (44+15i). -/
theorem gaussianInt2161PlusResidueMap_ker :
    RingHom.ker gaussianInt2161PlusResidueMap = Ideal.span {piPlus} := by
  have hker : (RingHom.ker gaussianInt2161PlusResidueMap).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective gaussianInt2161PlusResidueMap
      gaussianInt2161PlusResidueMap_surjective
  exact (Ideal.IsMaximal.eq_of_le piPlus_ideal_isMaximal hker.ne_top
    gaussianInt2161Plus_ideal_le_ker).symm

/-- The actual residue quotient Z[i]/(44+15i) = ZMod 2161. -/
noncomputable def gaussianInt2161PlusResidueEquiv :
    (GaussianInt ⧸ Ideal.span {piPlus}) ≃+* ZMod 2161 :=
  (Ideal.quotEquivOfEq gaussianInt2161PlusResidueMap_ker.symm).trans
    (RingHom.quotientKerEquivOfSurjective gaussianInt2161PlusResidueMap_surjective)

/-- The residue map at 44-15i, sending i to 147. -/
noncomputable def gaussianInt2161MinusResidueMap : GaussianInt →+* ZMod 2161 :=
  Zsqrtd.lift ⟨(147 : ZMod 2161), by decide⟩

/-- The conjugate residue map kills 44-15i. -/
theorem gaussianInt2161MinusResidueMap_generator :
    gaussianInt2161MinusResidueMap piMinus = 0 := by
  simp [gaussianInt2161MinusResidueMap, piMinus]
  decide

/-- The conjugate residue map is surjective. -/
theorem gaussianInt2161MinusResidueMap_surjective :
    Function.Surjective gaussianInt2161MinusResidueMap := by
  intro y
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective y
  refine ⟨(a : GaussianInt), ?_⟩
  simp [gaussianInt2161MinusResidueMap]

/-- The ideal (44-15i) is contained in the kernel of the conjugate map. -/
theorem gaussianInt2161Minus_ideal_le_ker :
    Ideal.span {piMinus} ≤ RingHom.ker gaussianInt2161MinusResidueMap := by
  refine Ideal.span_le.mpr ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact (RingHom.mem_ker).mpr gaussianInt2161MinusResidueMap_generator

/-- The kernel of the conjugate residue map is (44-15i). -/
theorem gaussianInt2161MinusResidueMap_ker :
    RingHom.ker gaussianInt2161MinusResidueMap = Ideal.span {piMinus} := by
  have hker : (RingHom.ker gaussianInt2161MinusResidueMap).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective gaussianInt2161MinusResidueMap
      gaussianInt2161MinusResidueMap_surjective
  exact (Ideal.IsMaximal.eq_of_le piMinus_ideal_isMaximal hker.ne_top
    gaussianInt2161Minus_ideal_le_ker).symm

/-- The actual residue quotient Z[i]/(44-15i) = ZMod 2161. -/
noncomputable def gaussianInt2161MinusResidueEquiv :
    (GaussianInt ⧸ Ideal.span {piMinus}) ≃+* ZMod 2161 :=
  (Ideal.quotEquivOfEq gaussianInt2161MinusResidueMap_ker.symm).trans
    (RingHom.quotientKerEquivOfSurjective gaussianInt2161MinusResidueMap_surjective)

/-! ## 3. Transport of the 2161 primes to the ring of integers -/

/-- The transported prime (44+15i) in the Gaussian ring of integers. -/
noncomputable def gaussianField2161PrimePlus : Ideal gaussianO :=
  Ideal.comap gaussianRingOfIntegersEquivGaussianInt.toRingHom (Ideal.span {piPlus})

/-- The transported (44+15i) is maximal. -/
instance gaussianField2161PrimePlus_isMaximal : gaussianField2161PrimePlus.IsMaximal :=
  Ideal.comap_isMaximal_of_equiv gaussianRingOfIntegersEquivGaussianInt

/-- The transported prime (44-15i) in the Gaussian ring of integers. -/
noncomputable def gaussianField2161PrimeMinus : Ideal gaussianO :=
  Ideal.comap gaussianRingOfIntegersEquivGaussianInt.toRingHom (Ideal.span {piMinus})

/-- The transported (44-15i) is maximal. -/
instance gaussianField2161PrimeMinus_isMaximal : gaussianField2161PrimeMinus.IsMaximal :=
  Ideal.comap_isMaximal_of_equiv gaussianRingOfIntegersEquivGaussianInt

/-- The actual residue quotient of the transported plus prime is ZMod 2161. -/
noncomputable def gaussianField2161PrimePlusResidueEquiv :
    (gaussianO ⧸ gaussianField2161PrimePlus) ≃+* ZMod 2161 :=
  (Ideal.quotientEquiv (gaussianField2161PrimePlus)
    (Ideal.span {piPlus})
    gaussianRingOfIntegersEquivGaussianInt
    (by
      change Ideal.span {piPlus} =
        Ideal.map gaussianRingOfIntegersEquivGaussianInt.toRingHom
          gaussianField2161PrimePlus
      rw [gaussianField2161PrimePlus,
        Ideal.map_comap_of_surjective
          gaussianRingOfIntegersEquivGaussianInt.toRingHom
          gaussianRingOfIntegersEquivGaussianInt.surjective])).trans
    gaussianInt2161PlusResidueEquiv

/-- The actual residue quotient of the transported minus prime is ZMod 2161. -/
noncomputable def gaussianField2161PrimeMinusResidueEquiv :
    (gaussianO ⧸ gaussianField2161PrimeMinus) ≃+* ZMod 2161 :=
  (Ideal.quotientEquiv (gaussianField2161PrimeMinus)
    (Ideal.span {piMinus})
    gaussianRingOfIntegersEquivGaussianInt
    (by
      change Ideal.span {piMinus} =
        Ideal.map gaussianRingOfIntegersEquivGaussianInt.toRingHom
          gaussianField2161PrimeMinus
      rw [gaussianField2161PrimeMinus,
        Ideal.map_comap_of_surjective
          gaussianRingOfIntegersEquivGaussianInt.toRingHom
          gaussianRingOfIntegersEquivGaussianInt.surjective])).trans
    gaussianInt2161MinusResidueEquiv

/-- The Gaussian integer 2161 lies in (44+15i). -/
theorem gaussianInt_2161_mem_piPlus_ideal :
    (2161 : GaussianInt) ∈ Ideal.span {piPlus} := by
  rw [← piPlus_mul_piMinus]
  exact Ideal.mul_mem_right piMinus _ (Ideal.subset_span (Set.mem_singleton_iff.mpr rfl))

/-- The Gaussian integer 2161 lies in (44-15i). -/
theorem gaussianInt_2161_mem_piMinus_ideal :
    (2161 : GaussianInt) ∈ Ideal.span {piMinus} := by
  rw [← piPlus_mul_piMinus]
  exact Ideal.mul_mem_left (Ideal.span {piMinus}) piPlus
    (Ideal.subset_span (Set.mem_singleton_iff.mpr rfl))

/-! ## 4. The rational prime ideal (2161) -/

/-- The concrete height-one prime at 2161 is the principal ideal (2161). -/
theorem concrete2161HeightOne_asIdeal_eq_span :
    concrete2161HeightOne.asIdeal =
      Ideal.span {(2161 : rationalO)} := by
  let e : rationalO ≃+* ℤ := Rat.IsIntegralClosure.intEquiv rationalO
  have h := Rat.HeightOneSpectrum.span_natGenerator
    (R := rationalO) concrete2161HeightOne
  rw [concrete2161HeightOne_natGenerator] at h
  change Ideal.span {(2161 : ℤ)} =
    Ideal.map e.toRingHom concrete2161HeightOne.asIdeal at h
  have h' := congrArg (Ideal.map e.symm.toRingHom) h
  rw [Ideal.map_span] at h'
  simp only [Set.image_singleton] at h'
  simp at h'
  exact h'.symm

/-- The rational principal ideal (2161) is maximal. -/
theorem gaussianRational2161_span_isMaximal :
    (Ideal.span {(2161 : rationalO)}).IsMaximal := by
  let e : rationalO ≃+* ℤ := Rat.IsIntegralClosure.intEquiv rationalO
  have hpZ : (Ideal.span {(2161 : ℤ)}).IsMaximal := by
    have hp2161 : (Ideal.span {(2161 : ℤ)}).IsPrime := by
      rw [Ideal.span_singleton_prime (by norm_num : (2161 : ℤ) ≠ 0)]
      rw [Int.prime_iff_natAbs_prime]
      norm_num
    exact hp2161.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; norm_num)
  have hmap : Ideal.map e.symm.toRingHom (Ideal.span {(2161 : ℤ)}) =
      Ideal.span {(2161 : rationalO)} := by
    rw [Ideal.map_span]
    simp only [Set.image_singleton]
    congr 1
    simp
  rw [← hmap]
  exact Ideal.map_isMaximal_of_equiv e.symm

/-! ## 5. The rational contractions of the transported primes -/

/-- The transported plus prime contracts to (2161) in the rational ring. -/
theorem gaussianField2161PrimePlus_under_rational :
    gaussianField2161PrimePlus.under rationalO =
      Ideal.span {(2161 : rationalO)} := by
  haveI : gaussianField2161PrimePlus.IsPrime :=
    gaussianField2161PrimePlus_isMaximal.isPrime
  have hle : Ideal.span {(2161 : rationalO)} ≤
      gaussianField2161PrimePlus.under rationalO := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    change (2161 : rationalO) ∈
      Ideal.comap (algebraMap rationalO gaussianO) gaussianField2161PrimePlus
    rw [Ideal.mem_comap]
    have h2161 : algebraMap rationalO gaussianO (2161 : rationalO) =
        (2161 : gaussianO) := map_natCast _ 2161
    rw [h2161]
    rw [gaussianField2161PrimePlus, Ideal.mem_comap]
    have he2161 : gaussianRingOfIntegersEquivGaussianInt.toRingHom
        (2161 : gaussianO) = (2161 : GaussianInt) := map_natCast _ 2161
    rw [he2161]
    exact gaussianInt_2161_mem_piPlus_ideal
  have hne : gaussianField2161PrimePlus.under rationalO ≠ ⊤ := by
    intro h
    have h1 : (1 : rationalO) ∈ gaussianField2161PrimePlus.under rationalO := by
      rw [h]; exact Submodule.mem_top
    change (1 : rationalO) ∈
      Ideal.comap (algebraMap rationalO gaussianO) gaussianField2161PrimePlus at h1
    rw [Ideal.mem_comap] at h1
    have hone : (1 : gaussianO) ∈ gaussianField2161PrimePlus := by
      simpa using h1
    have htop : (⊤ : Ideal gaussianO) ≤ gaussianField2161PrimePlus := by
      rw [top_le_iff, Ideal.eq_top_iff_one]
      exact hone
    exact gaussianField2161PrimePlus_isMaximal.ne_top (top_le_iff.mp htop)
  exact (Ideal.IsMaximal.eq_of_le gaussianRational2161_span_isMaximal hne hle).symm

/-- The transported minus prime contracts to (2161) in the rational ring. -/
theorem gaussianField2161PrimeMinus_under_rational :
    gaussianField2161PrimeMinus.under rationalO =
      Ideal.span {(2161 : rationalO)} := by
  haveI : gaussianField2161PrimeMinus.IsPrime :=
    gaussianField2161PrimeMinus_isMaximal.isPrime
  have h2161mem : (2161 : GaussianInt) ∈ Ideal.span {piMinus} :=
    gaussianInt_2161_mem_piMinus_ideal
  have hle : Ideal.span {(2161 : rationalO)} ≤
      gaussianField2161PrimeMinus.under rationalO := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    change (2161 : rationalO) ∈
      Ideal.comap (algebraMap rationalO gaussianO) gaussianField2161PrimeMinus
    rw [Ideal.mem_comap]
    have h2161 : algebraMap rationalO gaussianO (2161 : rationalO) =
        (2161 : gaussianO) := map_natCast _ 2161
    rw [h2161]
    rw [gaussianField2161PrimeMinus, Ideal.mem_comap]
    have he2161 : gaussianRingOfIntegersEquivGaussianInt.toRingHom
        (2161 : gaussianO) = (2161 : GaussianInt) := map_natCast _ 2161
    rw [he2161]
    exact h2161mem
  have hne : gaussianField2161PrimeMinus.under rationalO ≠ ⊤ := by
    intro h
    have h1 : (1 : rationalO) ∈ gaussianField2161PrimeMinus.under rationalO := by
      rw [h]; exact Submodule.mem_top
    change (1 : rationalO) ∈
      Ideal.comap (algebraMap rationalO gaussianO) gaussianField2161PrimeMinus at h1
    rw [Ideal.mem_comap] at h1
    have hone : (1 : gaussianO) ∈ gaussianField2161PrimeMinus := by
      simpa using h1
    have htop : (⊤ : Ideal gaussianO) ≤ gaussianField2161PrimeMinus := by
      rw [top_le_iff, Ideal.eq_top_iff_one]
      exact hone
    exact gaussianField2161PrimeMinus_isMaximal.ne_top (top_le_iff.mp htop)
  exact (Ideal.IsMaximal.eq_of_le gaussianRational2161_span_isMaximal hne hle).symm

/-! ## 6. Height-one spectra and the four finite places -/

/-- A height-one spectrum from a maximal ideal. -/
noncomputable def heightOneOfMaximal (P : Ideal gaussianO) [hP : P.IsMaximal] :
    IsDedekindDomain.HeightOneSpectrum gaussianO where
  asIdeal := P
  isPrime := hP.isPrime
  ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField hP
    (NumberField.RingOfIntegers.not_isField GaussianField)

/-- The finite place above 5 corresponding to the transported (2+i). -/
noncomputable def gaussianPlaceFivePlus : NumberField.FinitePlace GaussianField :=
  NumberField.FinitePlace.mk (heightOneOfMaximal gaussianFieldFivePrimePlus)

/-- The finite place above 5 corresponding to the transported (2-i). -/
noncomputable def gaussianPlaceFiveMinus : NumberField.FinitePlace GaussianField :=
  NumberField.FinitePlace.mk (heightOneOfMaximal gaussianFieldFivePrimeMinus)

/-- The finite place above 2161 corresponding to the transported (44+15i). -/
noncomputable def gaussianPlace2161Plus : NumberField.FinitePlace GaussianField :=
  NumberField.FinitePlace.mk (heightOneOfMaximal gaussianField2161PrimePlus)

/-- The finite place above 2161 corresponding to the transported (44-15i). -/
noncomputable def gaussianPlace2161Minus : NumberField.FinitePlace GaussianField :=
  NumberField.FinitePlace.mk (heightOneOfMaximal gaussianField2161PrimeMinus)

@[simp] theorem gaussianPlaceFivePlus_maximalIdeal :
    gaussianPlaceFivePlus.maximalIdeal =
      heightOneOfMaximal gaussianFieldFivePrimePlus :=
  NumberField.FinitePlace.maximalIdeal_mk _

@[simp] theorem gaussianPlaceFiveMinus_maximalIdeal :
    gaussianPlaceFiveMinus.maximalIdeal =
      heightOneOfMaximal gaussianFieldFivePrimeMinus :=
  NumberField.FinitePlace.maximalIdeal_mk _

@[simp] theorem gaussianPlace2161Plus_maximalIdeal :
    gaussianPlace2161Plus.maximalIdeal =
      heightOneOfMaximal gaussianField2161PrimePlus :=
  NumberField.FinitePlace.maximalIdeal_mk _

@[simp] theorem gaussianPlace2161Minus_maximalIdeal :
    gaussianPlace2161Minus.maximalIdeal =
      heightOneOfMaximal gaussianField2161PrimeMinus :=
  NumberField.FinitePlace.maximalIdeal_mk _

/-! ## 7. Contractions to the rational places -/

/-- The plus place above 5 contracts to the concrete rational place at 5. -/
theorem gaussianPlaceFivePlus_comap :
    NumberFieldFinitePlace.comap (k := ℚ) gaussianPlaceFivePlus = concreteFivePlace := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NumberFieldFinitePlace.comap_maximalIdeal, gaussianPlaceFivePlus_maximalIdeal]
  change gaussianFieldFivePrimePlus.under rationalO = concreteFivePlace.maximalIdeal.asIdeal
  rw [gaussianFieldFivePrimePlus_under_rational, concreteFivePlace_maximalIdeal,
    concreteFiveHeightOne_asIdeal_eq_span]

/-- The minus place above 5 contracts to the concrete rational place at 5. -/
theorem gaussianPlaceFiveMinus_comap :
    NumberFieldFinitePlace.comap (k := ℚ) gaussianPlaceFiveMinus = concreteFivePlace := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NumberFieldFinitePlace.comap_maximalIdeal, gaussianPlaceFiveMinus_maximalIdeal]
  change gaussianFieldFivePrimeMinus.under rationalO = concreteFivePlace.maximalIdeal.asIdeal
  rw [gaussianFieldFivePrimeMinus_under_rational, concreteFivePlace_maximalIdeal,
    concreteFiveHeightOne_asIdeal_eq_span]

/-- The plus place above 2161 contracts to the actual rational place at 2161. -/
theorem gaussianPlace2161Plus_comap :
    NumberFieldFinitePlace.comap (k := ℚ) gaussianPlace2161Plus = S2687Place := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NumberFieldFinitePlace.comap_maximalIdeal, gaussianPlace2161Plus_maximalIdeal]
  change gaussianField2161PrimePlus.under rationalO = S2687Place.maximalIdeal.asIdeal
  rw [gaussianField2161PrimePlus_under_rational, S2687Place_maximalIdeal,
    concrete2161HeightOne_asIdeal_eq_span]

/-- The minus place above 2161 contracts to the actual rational place at 2161. -/
theorem gaussianPlace2161Minus_comap :
    NumberFieldFinitePlace.comap (k := ℚ) gaussianPlace2161Minus = S2687Place := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NumberFieldFinitePlace.comap_maximalIdeal, gaussianPlace2161Minus_maximalIdeal]
  change gaussianField2161PrimeMinus.under rationalO = S2687Place.maximalIdeal.asIdeal
  rw [gaussianField2161PrimeMinus_under_rational, S2687Place_maximalIdeal,
    concrete2161HeightOne_asIdeal_eq_span]

/-! ## 8. Residue characteristics and oddness -/

/-- Ring characteristics are invariant under ring equivalence. -/
theorem ringChar_eq_of_ringEquiv {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (e : R ≃+* S) : ringChar R = ringChar S := by
  rw [ringChar.eq_iff]
  exact (RingHom.charP_iff e.toRingHom e.injective (ringChar S)).mpr (ringChar.charP S)

/-- The residue characteristic of the plus place above 5 is 5. -/
theorem gaussianPlaceFivePlus_residueCharacteristic :
    NumberFieldFinitePlace.residueCharacteristic gaussianPlaceFivePlus = 5 := by
  rw [NumberFieldFinitePlace.residueCharacteristic]
  change ringChar (gaussianO ⧸ (gaussianPlaceFivePlus.maximalIdeal : Ideal gaussianO)) = 5
  rw [gaussianPlaceFivePlus_maximalIdeal]
  change ringChar (gaussianO ⧸ gaussianFieldFivePrimePlus) = 5
  calc ringChar (gaussianO ⧸ gaussianFieldFivePrimePlus)
      = ringChar (ZMod 5) :=
        ringChar_eq_of_ringEquiv gaussianFieldFivePrimePlusResidueEquiv
    _ = 5 := ZMod.ringChar_zmod_n 5

/-- The residue characteristic of the minus place above 5 is 5. -/
theorem gaussianPlaceFiveMinus_residueCharacteristic :
    NumberFieldFinitePlace.residueCharacteristic gaussianPlaceFiveMinus = 5 := by
  rw [NumberFieldFinitePlace.residueCharacteristic]
  change ringChar (gaussianO ⧸ (gaussianPlaceFiveMinus.maximalIdeal : Ideal gaussianO)) = 5
  rw [gaussianPlaceFiveMinus_maximalIdeal]
  change ringChar (gaussianO ⧸ gaussianFieldFivePrimeMinus) = 5
  calc ringChar (gaussianO ⧸ gaussianFieldFivePrimeMinus)
      = ringChar (ZMod 5) :=
        ringChar_eq_of_ringEquiv gaussianFieldFivePrimeMinusResidueEquiv
    _ = 5 := ZMod.ringChar_zmod_n 5

/-- The residue characteristic of the plus place above 2161 is 2161. -/
theorem gaussianPlace2161Plus_residueCharacteristic :
    NumberFieldFinitePlace.residueCharacteristic gaussianPlace2161Plus = 2161 := by
  rw [NumberFieldFinitePlace.residueCharacteristic]
  change ringChar (gaussianO ⧸ (gaussianPlace2161Plus.maximalIdeal : Ideal gaussianO)) = 2161
  rw [gaussianPlace2161Plus_maximalIdeal]
  change ringChar (gaussianO ⧸ gaussianField2161PrimePlus) = 2161
  calc ringChar (gaussianO ⧸ gaussianField2161PrimePlus)
      = ringChar (ZMod 2161) :=
        ringChar_eq_of_ringEquiv gaussianField2161PrimePlusResidueEquiv
    _ = 2161 := ZMod.ringChar_zmod_n 2161

/-- The residue characteristic of the minus place above 2161 is 2161. -/
theorem gaussianPlace2161Minus_residueCharacteristic :
    NumberFieldFinitePlace.residueCharacteristic gaussianPlace2161Minus = 2161 := by
  rw [NumberFieldFinitePlace.residueCharacteristic]
  change ringChar (gaussianO ⧸ (gaussianPlace2161Minus.maximalIdeal : Ideal gaussianO)) = 2161
  rw [gaussianPlace2161Minus_maximalIdeal]
  change ringChar (gaussianO ⧸ gaussianField2161PrimeMinus) = 2161
  calc ringChar (gaussianO ⧸ gaussianField2161PrimeMinus)
      = ringChar (ZMod 2161) :=
        ringChar_eq_of_ringEquiv gaussianField2161PrimeMinusResidueEquiv
    _ = 2161 := ZMod.ringChar_zmod_n 2161

theorem gaussianPlaceFivePlus_odd :
    Odd (NumberFieldFinitePlace.residueCharacteristic gaussianPlaceFivePlus) := by
  rw [gaussianPlaceFivePlus_residueCharacteristic]
  norm_num

theorem gaussianPlaceFiveMinus_odd :
    Odd (NumberFieldFinitePlace.residueCharacteristic gaussianPlaceFiveMinus) := by
  rw [gaussianPlaceFiveMinus_residueCharacteristic]
  norm_num

theorem gaussianPlace2161Plus_odd :
    Odd (NumberFieldFinitePlace.residueCharacteristic gaussianPlace2161Plus) := by
  rw [gaussianPlace2161Plus_residueCharacteristic]
  norm_num

theorem gaussianPlace2161Minus_odd :
    Odd (NumberFieldFinitePlace.residueCharacteristic gaussianPlace2161Minus) := by
  rw [gaussianPlace2161Minus_residueCharacteristic]
  norm_num

/-! ## 9. Split multiplicative reduction at the four places -/

theorem gaussianPlaceFivePlus_split :
    (concreteSplitPuncturedCurve.baseChange GaussianField).HasSplitMultiplicativeReductionAt
      gaussianPlaceFivePlus :=
  S2702_split_over_five gaussianPlaceFivePlus gaussianPlaceFivePlus_comap

theorem gaussianPlaceFiveMinus_split :
    (concreteSplitPuncturedCurve.baseChange GaussianField).HasSplitMultiplicativeReductionAt
      gaussianPlaceFiveMinus :=
  S2702_split_over_five gaussianPlaceFiveMinus gaussianPlaceFiveMinus_comap

theorem gaussianPlace2161Plus_split :
    (concreteSplitPuncturedCurve.baseChange GaussianField).HasSplitMultiplicativeReductionAt
      gaussianPlace2161Plus :=
  S2702_split_over_2161 gaussianPlace2161Plus gaussianPlace2161Plus_comap

theorem gaussianPlace2161Minus_split :
    (concreteSplitPuncturedCurve.baseChange GaussianField).HasSplitMultiplicativeReductionAt
      gaussianPlace2161Minus :=
  S2702_split_over_2161 gaussianPlace2161Minus gaussianPlace2161Minus_comap

/-- The four-place datum for the Gaussian field, with the four actual primes. -/
noncomputable def S2703FourPlaceData : S2696FourPlaceData where
  p5a := gaussianPlaceFivePlus
  p5b := gaussianPlaceFiveMinus
  p2161a := gaussianPlace2161Plus
  p2161b := gaussianPlace2161Minus
  odd5a := gaussianPlaceFivePlus_odd
  odd5b := gaussianPlaceFiveMinus_odd
  odd2161a := gaussianPlace2161Plus_odd
  odd2161b := gaussianPlace2161Minus_odd

/-- Split multiplicative reduction at every member of the four-place datum. -/
theorem S2703_fourPlace_split
    (p : NumberField.FinitePlace GaussianField)
    (hp : p ∈ S2696Vbad S2703FourPlaceData) :
    (concreteSplitPuncturedCurve.baseChange GaussianField).HasSplitMultiplicativeReductionAt p := by
  rcases hp with rfl | rfl | rfl | rfl
  · exact gaussianPlaceFivePlus_split
  · exact gaussianPlaceFiveMinus_split
  · exact gaussianPlace2161Plus_split
  · exact gaussianPlace2161Minus_split

/-! ## 10. The valuation bridge -/

/-- The valuation bridge at the level of the completed valuation ring: a
number-ring element in the maximal ideal has value < 1 in the completion. -/
theorem valuation_algebraMap_completionIntegers_lt_one
    (p : NumberField.FinitePlace GaussianField)
    (π : NumberField.RingOfIntegers GaussianField)
    (h : π ∈ p.maximalIdeal.asIdeal) :
    Valued.v (((algebraMap (NumberField.RingOfIntegers GaussianField)
      (NumberFieldFinitePlace.CompletionIntegers p) π :
        NumberFieldFinitePlace.CompletionIntegers p) :
          NumberFieldFinitePlace.Completion p)) < 1 := by
  rw [NumberFieldFinitePlace.valued_algebraMap_completionIntegers]
  exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
    (v := p.maximalIdeal) (K := GaussianField) π).mpr h

/-- If a number-ring element lies in the maximal ideal of a finite place, its
image in the completed field has value < 1. -/
theorem valuation_algebraMap_completion_lt_one
    (p : NumberField.FinitePlace GaussianField)
    (π : NumberField.RingOfIntegers GaussianField)
    (h : π ∈ p.maximalIdeal.asIdeal) :
    Valued.v (algebraMap (NumberField.RingOfIntegers GaussianField)
      (NumberFieldFinitePlace.Completion p) π) < 1 := by
  change Valued.v (algebraMap GaussianField
    ((NumberFieldFinitePlace.underlyingPrime p).adicCompletion GaussianField)
    (algebraMap (NumberField.RingOfIntegers GaussianField) GaussianField π)) < 1
  change Valued.v ((algebraMap (NumberField.RingOfIntegers GaussianField)
    GaussianField π : GaussianField) :
      (NumberFieldFinitePlace.underlyingPrime p).adicCompletion GaussianField) < 1
  rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
    (v := NumberFieldFinitePlace.underlyingPrime p)]
  exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
    (v := p.maximalIdeal) (K := GaussianField) π).mpr h

/-! ## 11. Norm bridge from the explicit residue quotient -/

/-- The absolute norm of (44+15i) is 2161. -/
theorem piPlus_ideal_absNorm : (Ideal.span {piPlus}).absNorm = 2161 := by
  rw [Ideal.absNorm_apply]
  change Submodule.cardQuot (Ideal.span {piPlus}) = 2161
  rw [Submodule.cardQuot_apply]
  calc Nat.card (GaussianInt ⧸ Ideal.span {piPlus})
      = Nat.card (ZMod 2161) :=
        Nat.card_congr gaussianInt2161PlusResidueEquiv.toEquiv
    _ = 2161 := Nat.card_zmod 2161

/-- The algebra norm of piPlus recovers 2161, bridging Algebra.norm and
Zsqrtd.norm through the residue quotient. -/
theorem piPlus_algebraNorm_natAbs : (Algebra.norm ℤ piPlus).natAbs = 2161 := by
  rw [← Ideal.absNorm_span_singleton, piPlus_ideal_absNorm]

#print axioms piPlus_irreducible
#print axioms piPlus_ideal_isPrime
#print axioms gaussianPlaceFivePlus_comap
#print axioms gaussianPlaceFiveMinus_comap
#print axioms gaussianPlace2161Plus_comap
#print axioms gaussianPlace2161Minus_comap
#print axioms gaussianPlaceFivePlus_residueCharacteristic
#print axioms gaussianPlace2161Plus_residueCharacteristic
#print axioms gaussianPlaceFivePlus_split
#print axioms gaussianPlace2161Minus_split
#print axioms S2703_fourPlace_split
#print axioms valuation_algebraMap_completion_lt_one

end LeanFormal.IUT.XiFPaper.S2703GaussianPrimePlacesActual
end
