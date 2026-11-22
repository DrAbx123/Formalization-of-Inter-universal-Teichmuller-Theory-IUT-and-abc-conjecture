import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianIntegralBasis
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

/-!
# S2705: the Gaussian prime ideals above 5

The Gaussian integers Z[i] contain the two explicit elements
2 + i and 2 - i, both of norm 5 = 2^2 + 1^2.  Since 5
is prime, both elements are irreducible, so the principal ideals they
generate are maximal in the Euclidean domain Z[i].

The two maximal ideals are then mapped along the actual ring-of-integers
equivalence GaussianInt = NumberField.RingOfIntegers GaussianField and
give two finite places of the Gaussian field.  Their residue fields are
identified with ZMod 5, hence both residue characteristics are 5
(and odd).

The proof is complete: no proof holes and no extra axioms.
-/

namespace LeanFormal.IUT.XiFPaper.S2705GaussianFivePlacesActual

local instance s2705GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s2705Fact5 : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The ring of integers of the Gaussian field. -/
abbrev GaussianO : Type := NumberField.RingOfIntegers GaussianField

/-- The rational prime 5 is prime. -/
theorem natPrime5 : Nat.Prime 5 := Nat.prime_five

/-! ## 1. The two Gaussian integers of norm 5 -/

/-- The Gaussian integer 2 + i. -/
def gaussianInt5Plus : GaussianInt := ⟨2, 1⟩

/-- The Gaussian integer 2 - i. -/
def gaussianInt5Minus : GaussianInt := ⟨2, -1⟩

/-- The norm of 2 + i is 5 = 2^2 + 1^2. -/
theorem gaussianInt5Plus_norm :
    Zsqrtd.norm gaussianInt5Plus = 5 := by
  simp [gaussianInt5Plus, Zsqrtd.norm_def]

/-- The norm of 2 - i is 5 = 2^2 + 1^2. -/
theorem gaussianInt5Minus_norm :
    Zsqrtd.norm gaussianInt5Minus = 5 := by
  simp [gaussianInt5Minus, Zsqrtd.norm_def]

/-- The actual factorization (2 + i)(2 - i) = 5. -/
theorem gaussianInt5Plus_mul_minus :
    gaussianInt5Plus * gaussianInt5Minus = (5 : GaussianInt) := by
  apply Zsqrtd.ext_iff.mpr
  constructor <;> norm_num [gaussianInt5Plus, gaussianInt5Minus]

/-- The principal-ideal factorization (5) = (2+i)(2-i). -/
theorem gaussianInt5_ideal_factorization :
    Ideal.span {(5 : GaussianInt)} =
      Ideal.span {gaussianInt5Plus} * Ideal.span {gaussianInt5Minus} := by
  rw [← gaussianInt5Plus_mul_minus]
  exact (Ideal.span_singleton_mul_span_singleton _ _).symm

/-- 5 lies in the ideal (2 + i). -/
theorem gaussianInt5_mem_plus :
    (5 : GaussianInt) ∈ Ideal.span {gaussianInt5Plus} := by
  rw [← gaussianInt5Plus_mul_minus]
  exact Ideal.mul_mem_right gaussianInt5Minus _
    (Ideal.subset_span (Set.mem_singleton_iff.mpr rfl))

/-- 5 lies in the ideal (2 - i). -/
theorem gaussianInt5_mem_minus :
    (5 : GaussianInt) ∈ Ideal.span {gaussianInt5Minus} := by
  rw [Ideal.mem_span_singleton]
  exact ⟨gaussianInt5Plus, by
    rw [mul_comm, gaussianInt5Plus_mul_minus]⟩

/-! ## 2. Irreducibility and maximality in Z[i] -/

/-- 2 + i is irreducible: its norm is the prime 5. -/
theorem gaussianInt5Plus_irreducible : Irreducible gaussianInt5Plus := by
  rw [irreducible_iff]
  constructor
  · intro hunit
    have hnorm : (Zsqrtd.norm gaussianInt5Plus).natAbs = 1 :=
      Zsqrtd.norm_eq_one_iff.mpr hunit
    rw [gaussianInt5Plus_norm] at hnorm
    norm_num at hnorm
  · intro a b hab
    have hnorm : (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs = 5 := by
      calc (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs
          = (Zsqrtd.norm (a * b)).natAbs := by rw [Zsqrtd.norm_mul, Int.natAbs_mul]
        _ = (Zsqrtd.norm gaussianInt5Plus).natAbs := by rw [hab]
        _ = 5 := by rw [gaussianInt5Plus_norm]; norm_num
    have hdvd : (Zsqrtd.norm a).natAbs ∣ 5 := ⟨(Zsqrtd.norm b).natAbs, hnorm.symm⟩
    have hcases := s2705Fact5.out.eq_one_or_self_of_dvd
      ((Zsqrtd.norm a).natAbs) hdvd
    rcases hcases with ha | ha
    · left
      exact Zsqrtd.norm_eq_one_iff.mp ha
    · right
      have hb : (Zsqrtd.norm b).natAbs = 1 := by
        rw [ha] at hnorm
        omega
      exact Zsqrtd.norm_eq_one_iff.mp hb

/-- 2 - i is irreducible: its norm is the prime 5. -/
theorem gaussianInt5Minus_irreducible : Irreducible gaussianInt5Minus := by
  rw [irreducible_iff]
  constructor
  · intro hunit
    have hnorm : (Zsqrtd.norm gaussianInt5Minus).natAbs = 1 :=
      Zsqrtd.norm_eq_one_iff.mpr hunit
    rw [gaussianInt5Minus_norm] at hnorm
    norm_num at hnorm
  · intro a b hab
    have hnorm : (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs = 5 := by
      calc (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs
          = (Zsqrtd.norm (a * b)).natAbs := by rw [Zsqrtd.norm_mul, Int.natAbs_mul]
        _ = (Zsqrtd.norm gaussianInt5Minus).natAbs := by rw [hab]
        _ = 5 := by rw [gaussianInt5Minus_norm]; norm_num
    have hdvd : (Zsqrtd.norm a).natAbs ∣ 5 := ⟨(Zsqrtd.norm b).natAbs, hnorm.symm⟩
    have hcases := s2705Fact5.out.eq_one_or_self_of_dvd
      ((Zsqrtd.norm a).natAbs) hdvd
    rcases hcases with ha | ha
    · left
      exact Zsqrtd.norm_eq_one_iff.mp ha
    · right
      have hb : (Zsqrtd.norm b).natAbs = 1 := by
        rw [ha] at hnorm
        omega
      exact Zsqrtd.norm_eq_one_iff.mp hb

/-- The principal ideal (2 + i) is maximal in Z[i]. -/
theorem gaussianInt5Plus_span_isMaximal :
    (Ideal.span {gaussianInt5Plus}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible gaussianInt5Plus_irreducible

instance gaussianInt5Plus_span_isMaximal_instance :
    (Ideal.span {gaussianInt5Plus}).IsMaximal :=
  gaussianInt5Plus_span_isMaximal

/-- The principal ideal (2 - i) is maximal in Z[i]. -/
theorem gaussianInt5Minus_span_isMaximal :
    (Ideal.span {gaussianInt5Minus}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible gaussianInt5Minus_irreducible

instance gaussianInt5Minus_span_isMaximal_instance :
    (Ideal.span {gaussianInt5Minus}).IsMaximal :=
  gaussianInt5Minus_span_isMaximal

/-- The coordinate linear equivalence Z[i] = Z x Z. -/
def gaussianIntEquivProd : GaussianInt ≃ₗ[ℤ] ℤ × ℤ where
  toFun x := (x.re, x.im)
  invFun p := (⟨p.1, p.2⟩ : GaussianInt)
  left_inv := by rintro ⟨a, b⟩; rfl
  right_inv := by rintro ⟨a, b⟩; rfl
  map_add' := by intro a b; ext <;> simp
  map_smul' := by intro n x; ext <;> simp [zsmul_eq_mul]

/-- Z[i] is a free Z-module of rank two. -/
instance gaussianIntModuleFree : Module.Free ℤ GaussianInt :=
  Module.Free.of_equiv' (inferInstance : Module.Free ℤ (ℤ × ℤ)) gaussianIntEquivProd.symm

/-! ## 3. Explicit residue maps Z[i] -> ZMod 5

We have 3^2 = -1 and 2 + 3 = 0 modulo 5, and
2^2 = -1 with 2 - 2 = 0 modulo 5.  Hence the two
residue maps below kill 2 + i and 2 - i respectively. -/

/-- The residue map Z[i] -> ZMod 5 sending i to 3. -/
noncomputable def gaussianInt5PlusResidueMap : GaussianInt →+* ZMod 5 :=
  Zsqrtd.lift ⟨(3 : ZMod 5), by decide⟩

/-- The residue map Z[i] -> ZMod 5 sending i to 2 = -3. -/
noncomputable def gaussianInt5MinusResidueMap : GaussianInt →+* ZMod 5 :=
  Zsqrtd.lift ⟨(2 : ZMod 5), by decide⟩

/-- The plus residue map kills 2 + i. -/
theorem gaussianInt5PlusResidueMap_generator :
    gaussianInt5PlusResidueMap gaussianInt5Plus = 0 := by
  simp [gaussianInt5PlusResidueMap, gaussianInt5Plus]
  decide

/-- The minus residue map kills 2 - i. -/
theorem gaussianInt5MinusResidueMap_generator :
    gaussianInt5MinusResidueMap gaussianInt5Minus = 0 := by
  simp [gaussianInt5MinusResidueMap, gaussianInt5Minus]

/-- The plus residue map is surjective, already on the integer classes. -/
theorem gaussianInt5PlusResidueMap_surjective :
    Function.Surjective gaussianInt5PlusResidueMap := by
  intro y
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective y
  refine ⟨(a : GaussianInt), ?_⟩
  simp [gaussianInt5PlusResidueMap]

/-- The minus residue map is surjective, already on the integer classes. -/
theorem gaussianInt5MinusResidueMap_surjective :
    Function.Surjective gaussianInt5MinusResidueMap := by
  intro y
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective y
  refine ⟨(a : GaussianInt), ?_⟩
  simp [gaussianInt5MinusResidueMap]

/-- The ideal (2 + i) is contained in the kernel of the plus residue map. -/
theorem gaussianInt5Plus_ideal_le_ker :
    Ideal.span {gaussianInt5Plus} ≤
      RingHom.ker gaussianInt5PlusResidueMap := by
  refine Ideal.span_le.mpr ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact (RingHom.mem_ker).mpr gaussianInt5PlusResidueMap_generator

/-- The ideal (2 - i) is contained in the kernel of the minus residue map. -/
theorem gaussianInt5Minus_ideal_le_ker :
    Ideal.span {gaussianInt5Minus} ≤
      RingHom.ker gaussianInt5MinusResidueMap := by
  refine Ideal.span_le.mpr ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact (RingHom.mem_ker).mpr gaussianInt5MinusResidueMap_generator

/-- The kernel of the plus residue map is exactly (2 + i). -/
theorem gaussianInt5PlusResidueMap_ker :
    RingHom.ker gaussianInt5PlusResidueMap =
      Ideal.span {gaussianInt5Plus} := by
  have hker : (RingHom.ker gaussianInt5PlusResidueMap).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective gaussianInt5PlusResidueMap
      gaussianInt5PlusResidueMap_surjective
  exact (Ideal.IsMaximal.eq_of_le gaussianInt5Plus_span_isMaximal hker.ne_top
    gaussianInt5Plus_ideal_le_ker).symm

/-- The kernel of the minus residue map is exactly (2 - i). -/
theorem gaussianInt5MinusResidueMap_ker :
    RingHom.ker gaussianInt5MinusResidueMap =
      Ideal.span {gaussianInt5Minus} := by
  have hker : (RingHom.ker gaussianInt5MinusResidueMap).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective gaussianInt5MinusResidueMap
      gaussianInt5MinusResidueMap_surjective
  exact (Ideal.IsMaximal.eq_of_le gaussianInt5Minus_span_isMaximal hker.ne_top
    gaussianInt5Minus_ideal_le_ker).symm

/-- The two principal ideals are distinct: the plus residue map sends
2 - i to 4, which is nonzero modulo 5. -/
theorem gaussianInt5Plus_ne_minus_span :
    Ideal.span {gaussianInt5Plus} ≠ Ideal.span {gaussianInt5Minus} := by
  intro h
  have hmem : gaussianInt5Minus ∈ Ideal.span {gaussianInt5Plus} := by
    rw [h]
    exact Ideal.subset_span (Set.mem_singleton_iff.mpr rfl)
  have hker : gaussianInt5Minus ∈ RingHom.ker gaussianInt5PlusResidueMap :=
    gaussianInt5Plus_ideal_le_ker hmem
  have hzero : gaussianInt5PlusResidueMap gaussianInt5Minus = 0 := hker
  have h4 : gaussianInt5PlusResidueMap gaussianInt5Minus = 4 := by
    simp [gaussianInt5PlusResidueMap, gaussianInt5Minus]
    decide
  rw [h4] at hzero
  exact (by decide : (4 : ZMod 5) ≠ 0) hzero

/-- The residue quotient Z[i]/(2+i) is ZMod 5. -/
noncomputable def gaussianInt5PlusResidueEquiv :
    (GaussianInt ⧸ Ideal.span {gaussianInt5Plus}) ≃+* ZMod 5 :=
  (Ideal.quotEquivOfEq gaussianInt5PlusResidueMap_ker.symm).trans
    (RingHom.quotientKerEquivOfSurjective gaussianInt5PlusResidueMap_surjective)

/-- The residue quotient Z[i]/(2-i) is ZMod 5. -/
noncomputable def gaussianInt5MinusResidueEquiv :
    (GaussianInt ⧸ Ideal.span {gaussianInt5Minus}) ≃+* ZMod 5 :=
  (Ideal.quotEquivOfEq gaussianInt5MinusResidueMap_ker.symm).trans
    (RingHom.quotientKerEquivOfSurjective gaussianInt5MinusResidueMap_surjective)

/-- The quotient Z[i]/(2+i) has 5 elements. -/
theorem gaussianInt5Plus_cardQuot :
    Nat.card (GaussianInt ⧸ Ideal.span {gaussianInt5Plus}) = 5 := by
  calc Nat.card (GaussianInt ⧸ Ideal.span {gaussianInt5Plus})
      = Nat.card (ZMod 5) :=
        Nat.card_congr gaussianInt5PlusResidueEquiv.toEquiv
    _ = 5 := Nat.card_zmod 5

/-- The quotient Z[i]/(2-i) has 5 elements. -/
theorem gaussianInt5Minus_cardQuot :
    Nat.card (GaussianInt ⧸ Ideal.span {gaussianInt5Minus}) = 5 := by
  calc Nat.card (GaussianInt ⧸ Ideal.span {gaussianInt5Minus})
      = Nat.card (ZMod 5) :=
        Nat.card_congr gaussianInt5MinusResidueEquiv.toEquiv
    _ = 5 := Nat.card_zmod 5

/-- The absolute norm of the principal ideal (2+i) in Z[i] is 5. -/
theorem gaussianInt5Plus_absNorm :
    Ideal.absNorm (Ideal.span {gaussianInt5Plus}) = 5 := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact gaussianInt5Plus_cardQuot

/-- The absolute norm of the principal ideal (2-i) in Z[i] is 5. -/
theorem gaussianInt5Minus_absNorm :
    Ideal.absNorm (Ideal.span {gaussianInt5Minus}) = 5 := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact gaussianInt5Minus_cardQuot

/-! ## 4. The corresponding ideals of the ring of integers -/

/-- The prime ideal of the ring of integers of the Gaussian field
corresponding to (2 + i). -/
noncomputable def gaussianField5Plus : Ideal GaussianO :=
  Ideal.comap gaussianRingOfIntegersEquivGaussianInt.toRingHom
    (Ideal.span {gaussianInt5Plus})

/-- The prime ideal of the ring of integers corresponding to (2 - i). -/
noncomputable def gaussianField5Minus : Ideal GaussianO :=
  Ideal.comap gaussianRingOfIntegersEquivGaussianInt.toRingHom
    (Ideal.span {gaussianInt5Minus})

/-- The image of (2+i) under the actual ring-of-integers equivalence. -/
theorem gaussianField5Plus_eq_map :
    gaussianField5Plus =
      Ideal.map gaussianIntEquivRingOfIntegers.toRingHom
        (Ideal.span {gaussianInt5Plus}) := by
  rw [gaussianField5Plus]
  exact (Ideal.map_symm (f := gaussianRingOfIntegersEquivGaussianInt)).symm

/-- The image of (2-i) under the actual ring-of-integers equivalence. -/
theorem gaussianField5Minus_eq_map :
    gaussianField5Minus =
      Ideal.map gaussianIntEquivRingOfIntegers.toRingHom
        (Ideal.span {gaussianInt5Minus}) := by
  rw [gaussianField5Minus]
  exact (Ideal.map_symm (f := gaussianRingOfIntegersEquivGaussianInt)).symm

/-- The transported plus ideal is maximal. -/
instance gaussianField5Plus_isMaximal : gaussianField5Plus.IsMaximal :=
  Ideal.comap_isMaximal_of_equiv gaussianRingOfIntegersEquivGaussianInt

/-- The transported minus ideal is maximal. -/
instance gaussianField5Minus_isMaximal : gaussianField5Minus.IsMaximal :=
  Ideal.comap_isMaximal_of_equiv gaussianRingOfIntegersEquivGaussianInt

/-- The two transported ideals are distinct. -/
theorem gaussianField5Plus_ne_minus :
    gaussianField5Plus ≠ gaussianField5Minus := by
  intro h
  have hmap := congrArg
    (Ideal.map gaussianRingOfIntegersEquivGaussianInt.toRingHom) h
  rw [gaussianField5Plus, gaussianField5Minus,
    Ideal.map_comap_of_surjective
      gaussianRingOfIntegersEquivGaussianInt.toRingHom
      gaussianRingOfIntegersEquivGaussianInt.surjective,
    Ideal.map_comap_of_surjective
      gaussianRingOfIntegersEquivGaussianInt.toRingHom
      gaussianRingOfIntegersEquivGaussianInt.surjective] at hmap
  exact gaussianInt5Plus_ne_minus_span hmap

/-- The residue quotient of the transported plus ideal is ZMod 5. -/
noncomputable def gaussianField5PlusResidueEquiv :
    (GaussianO ⧸ gaussianField5Plus) ≃+* ZMod 5 :=
  (Ideal.quotientEquiv (gaussianField5Plus)
    (Ideal.span {gaussianInt5Plus})
    gaussianRingOfIntegersEquivGaussianInt
    (by
      change Ideal.span {gaussianInt5Plus} =
        Ideal.map gaussianRingOfIntegersEquivGaussianInt.toRingHom
          gaussianField5Plus
      rw [gaussianField5Plus,
        Ideal.map_comap_of_surjective
          gaussianRingOfIntegersEquivGaussianInt.toRingHom
          gaussianRingOfIntegersEquivGaussianInt.surjective])).trans
    gaussianInt5PlusResidueEquiv

/-- The residue quotient of the transported minus ideal is ZMod 5. -/
noncomputable def gaussianField5MinusResidueEquiv :
    (GaussianO ⧸ gaussianField5Minus) ≃+* ZMod 5 :=
  (Ideal.quotientEquiv (gaussianField5Minus)
    (Ideal.span {gaussianInt5Minus})
    gaussianRingOfIntegersEquivGaussianInt
    (by
      change Ideal.span {gaussianInt5Minus} =
        Ideal.map gaussianRingOfIntegersEquivGaussianInt.toRingHom
          gaussianField5Minus
      rw [gaussianField5Minus,
        Ideal.map_comap_of_surjective
          gaussianRingOfIntegersEquivGaussianInt.toRingHom
          gaussianRingOfIntegersEquivGaussianInt.surjective])).trans
    gaussianInt5MinusResidueEquiv

/-- The absolute norm of the transported plus ideal is 5. -/
theorem gaussianField5Plus_absNorm :
    Ideal.absNorm gaussianField5Plus = 5 := by
  rw [Ideal.absNorm_apply]
  rw [Submodule.cardQuot_apply]
  calc Nat.card (GaussianO ⧸ gaussianField5Plus)
      = Nat.card (ZMod 5) :=
        Nat.card_congr gaussianField5PlusResidueEquiv.toEquiv
    _ = 5 := Nat.card_zmod 5

/-- The absolute norm of the transported minus ideal is 5. -/
theorem gaussianField5Minus_absNorm :
    Ideal.absNorm gaussianField5Minus = 5 := by
  rw [Ideal.absNorm_apply]
  rw [Submodule.cardQuot_apply]
  calc Nat.card (GaussianO ⧸ gaussianField5Minus)
      = Nat.card (ZMod 5) :=
        Nat.card_congr gaussianField5MinusResidueEquiv.toEquiv
    _ = 5 := Nat.card_zmod 5

/-! ## 5. The two finite places and their residue characteristics -/

/-- The finite place of the Gaussian field at (2 + i). -/
noncomputable def gaussianField5PlusPlace : NumberField.FinitePlace GaussianField :=
  NumberField.FinitePlace.mk
    { asIdeal := gaussianField5Plus
      isPrime := gaussianField5Plus_isMaximal.isPrime
      ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField
        gaussianField5Plus_isMaximal
        (NumberField.RingOfIntegers.not_isField GaussianField) }

/-- The finite place of the Gaussian field at (2 - i). -/
noncomputable def gaussianField5MinusPlace : NumberField.FinitePlace GaussianField :=
  NumberField.FinitePlace.mk
    { asIdeal := gaussianField5Minus
      isPrime := gaussianField5Minus_isMaximal.isPrime
      ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField
        gaussianField5Minus_isMaximal
        (NumberField.RingOfIntegers.not_isField GaussianField) }

/-- The maximal ideal of the plus place is the transported plus ideal. -/
theorem gaussianField5PlusPlace_maximalIdeal :
    gaussianField5PlusPlace.maximalIdeal.asIdeal = gaussianField5Plus :=
  congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
    (NumberField.FinitePlace.maximalIdeal_mk _)

/-- The maximal ideal of the minus place is the transported minus ideal. -/
theorem gaussianField5MinusPlace_maximalIdeal :
    gaussianField5MinusPlace.maximalIdeal.asIdeal = gaussianField5Minus :=
  congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
    (NumberField.FinitePlace.maximalIdeal_mk _)

/-- The two finite places are distinct. -/
theorem gaussianField5PlusPlace_ne_minusPlace :
    gaussianField5PlusPlace ≠ gaussianField5MinusPlace := by
  intro h
  have hmax := congrArg NumberField.FinitePlace.maximalIdeal h
  have hasIdeal := congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hmax
  rw [gaussianField5PlusPlace_maximalIdeal,
    gaussianField5MinusPlace_maximalIdeal] at hasIdeal
  exact gaussianField5Plus_ne_minus hasIdeal

/-- The residue characteristic of the plus place is 5. -/
theorem gaussianField5PlusPlace_residueCharacteristic :
    NumberFieldFinitePlace.residueCharacteristic gaussianField5PlusPlace = 5 := by
  rw [NumberFieldFinitePlace.residueCharacteristic]
  change ringChar (GaussianO ⧸ gaussianField5PlusPlace.maximalIdeal.asIdeal) = 5
  rw [gaussianField5PlusPlace_maximalIdeal]
  rw [ringChar.eq_iff]
  exact (RingHom.charP_iff
    (gaussianField5PlusResidueEquiv :
      (GaussianO ⧸ gaussianField5Plus) →+* ZMod 5)
    gaussianField5PlusResidueEquiv.injective 5).mpr inferInstance

/-- The residue characteristic of the minus place is 5. -/
theorem gaussianField5MinusPlace_residueCharacteristic :
    NumberFieldFinitePlace.residueCharacteristic gaussianField5MinusPlace = 5 := by
  rw [NumberFieldFinitePlace.residueCharacteristic]
  change ringChar (GaussianO ⧸ gaussianField5MinusPlace.maximalIdeal.asIdeal) = 5
  rw [gaussianField5MinusPlace_maximalIdeal]
  rw [ringChar.eq_iff]
  exact (RingHom.charP_iff
    (gaussianField5MinusResidueEquiv :
      (GaussianO ⧸ gaussianField5Minus) →+* ZMod 5)
    gaussianField5MinusResidueEquiv.injective 5).mpr inferInstance

/-- The residue characteristic of the plus place is odd. -/
theorem gaussianField5PlusPlace_residueCharacteristic_odd :
    Odd (NumberFieldFinitePlace.residueCharacteristic gaussianField5PlusPlace) := by
  rw [gaussianField5PlusPlace_residueCharacteristic]
  exact ⟨2, by norm_num⟩

/-- The residue characteristic of the minus place is odd. -/
theorem gaussianField5MinusPlace_residueCharacteristic_odd :
    Odd (NumberFieldFinitePlace.residueCharacteristic gaussianField5MinusPlace) := by
  rw [gaussianField5MinusPlace_residueCharacteristic]
  exact ⟨2, by norm_num⟩


/-! ## 6. The places over the rational prime 5 and split multiplicative reduction -/

/-- The height-one prime of the rational ring of integers at 5 is the
principal ideal generated by 5. -/
theorem concreteFiveHeightOne_asIdeal_eq_span :
    concreteFiveHeightOne.asIdeal =
      Ideal.span {(5 : NumberField.RingOfIntegers ℚ)} := by
  let e : NumberField.RingOfIntegers ℚ ≃+* ℤ :=
    Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)
  have h := Rat.HeightOneSpectrum.span_natGenerator
    (R := NumberField.RingOfIntegers ℚ) concreteFiveHeightOne
  rw [concreteFiveHeightOne_natGenerator] at h
  change Ideal.span {(5 : ℤ)} =
    Ideal.map e.toRingHom concreteFiveHeightOne.asIdeal at h
  have h' := congrArg (Ideal.map e.symm.toRingHom) h
  rw [Ideal.map_span] at h'
  simp only [Set.image_singleton] at h'
  simp at h'
  exact h'.symm

/-- 5 lies in the transported plus ideal. -/
theorem gaussianField5Plus_mem_natCast :
    (5 : GaussianO) ∈ gaussianField5Plus := by
  rw [gaussianField5Plus, Ideal.mem_comap]
  have h : gaussianRingOfIntegersEquivGaussianInt.toRingHom (5 : GaussianO) =
      (5 : GaussianInt) := map_natCast _ 5
  rw [h]
  exact gaussianInt5_mem_plus

/-- 5 lies in the transported minus ideal. -/
theorem gaussianField5Minus_mem_natCast :
    (5 : GaussianO) ∈ gaussianField5Minus := by
  rw [gaussianField5Minus, Ideal.mem_comap]
  have h : gaussianRingOfIntegersEquivGaussianInt.toRingHom (5 : GaussianO) =
      (5 : GaussianInt) := map_natCast _ 5
  rw [h]
  exact gaussianInt5_mem_minus

/-- The transported plus ideal lies over the rational prime ideal (5). -/
theorem gaussianField5Plus_under_rational :
    gaussianField5Plus.under (NumberField.RingOfIntegers ℚ) =
      Ideal.span {(5 : NumberField.RingOfIntegers ℚ)} := by
  have hle : Ideal.span {(5 : NumberField.RingOfIntegers ℚ)} ≤
      gaussianField5Plus.under (NumberField.RingOfIntegers ℚ) := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    change (5 : NumberField.RingOfIntegers ℚ) ∈
      Ideal.comap (algebraMap (NumberField.RingOfIntegers ℚ) GaussianO)
        gaussianField5Plus
    rw [Ideal.mem_comap]
    have h : algebraMap (NumberField.RingOfIntegers ℚ) GaussianO
        (5 : NumberField.RingOfIntegers ℚ) = (5 : GaussianO) :=
      map_natCast _ 5
    rw [h]
    exact gaussianField5Plus_mem_natCast
  have hne : gaussianField5Plus.under (NumberField.RingOfIntegers ℚ) ≠ ⊤ := by
    intro h
    have h1 : (1 : NumberField.RingOfIntegers ℚ) ∈
        gaussianField5Plus.under (NumberField.RingOfIntegers ℚ) := by
      rw [h]; exact Submodule.mem_top
    change (1 : NumberField.RingOfIntegers ℚ) ∈
      Ideal.comap (algebraMap (NumberField.RingOfIntegers ℚ) GaussianO)
        gaussianField5Plus at h1
    rw [Ideal.mem_comap] at h1
    have hone : (1 : GaussianO) ∈ gaussianField5Plus := by
      simpa using h1
    have htop : (⊤ : Ideal GaussianO) ≤ gaussianField5Plus := by
      rw [top_le_iff, Ideal.eq_top_iff_one]
      exact hone
    exact gaussianField5Plus_isMaximal.ne_top (top_le_iff.mp htop)
  have hmax : (Ideal.span {(5 : NumberField.RingOfIntegers ℚ)}).IsMaximal := by
    rw [← concreteFiveHeightOne_asIdeal_eq_span]
    exact concreteFiveHeightOne.isPrime.isMaximal concreteFiveHeightOne.ne_bot
  exact (Ideal.IsMaximal.eq_of_le hmax hne hle).symm

/-- The transported minus ideal lies over the rational prime ideal (5). -/
theorem gaussianField5Minus_under_rational :
    gaussianField5Minus.under (NumberField.RingOfIntegers ℚ) =
      Ideal.span {(5 : NumberField.RingOfIntegers ℚ)} := by
  have hle : Ideal.span {(5 : NumberField.RingOfIntegers ℚ)} ≤
      gaussianField5Minus.under (NumberField.RingOfIntegers ℚ) := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    change (5 : NumberField.RingOfIntegers ℚ) ∈
      Ideal.comap (algebraMap (NumberField.RingOfIntegers ℚ) GaussianO)
        gaussianField5Minus
    rw [Ideal.mem_comap]
    have h : algebraMap (NumberField.RingOfIntegers ℚ) GaussianO
        (5 : NumberField.RingOfIntegers ℚ) = (5 : GaussianO) :=
      map_natCast _ 5
    rw [h]
    exact gaussianField5Minus_mem_natCast
  have hne : gaussianField5Minus.under (NumberField.RingOfIntegers ℚ) ≠ ⊤ := by
    intro h
    have h1 : (1 : NumberField.RingOfIntegers ℚ) ∈
        gaussianField5Minus.under (NumberField.RingOfIntegers ℚ) := by
      rw [h]; exact Submodule.mem_top
    change (1 : NumberField.RingOfIntegers ℚ) ∈
      Ideal.comap (algebraMap (NumberField.RingOfIntegers ℚ) GaussianO)
        gaussianField5Minus at h1
    rw [Ideal.mem_comap] at h1
    have hone : (1 : GaussianO) ∈ gaussianField5Minus := by
      simpa using h1
    have htop : (⊤ : Ideal GaussianO) ≤ gaussianField5Minus := by
      rw [top_le_iff, Ideal.eq_top_iff_one]
      exact hone
    exact gaussianField5Minus_isMaximal.ne_top (top_le_iff.mp htop)
  have hmax : (Ideal.span {(5 : NumberField.RingOfIntegers ℚ)}).IsMaximal := by
    rw [← concreteFiveHeightOne_asIdeal_eq_span]
    exact concreteFiveHeightOne.isPrime.isMaximal concreteFiveHeightOne.ne_bot
  exact (Ideal.IsMaximal.eq_of_le hmax hne hle).symm

/-- The plus place restricts to the rational place at 5. -/
theorem gaussianField5PlusPlace_comap :
    NumberFieldFinitePlace.comap (k := ℚ) gaussianField5PlusPlace = concreteFivePlace := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NumberFieldFinitePlace.comap_maximalIdeal, gaussianField5PlusPlace_maximalIdeal]
  change gaussianField5Plus.under (NumberField.RingOfIntegers ℚ) =
    concreteFivePlace.maximalIdeal.asIdeal
  rw [gaussianField5Plus_under_rational, concreteFivePlace_maximalIdeal,
    concreteFiveHeightOne_asIdeal_eq_span]

/-- The minus place restricts to the rational place at 5. -/
theorem gaussianField5MinusPlace_comap :
    NumberFieldFinitePlace.comap (k := ℚ) gaussianField5MinusPlace = concreteFivePlace := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NumberFieldFinitePlace.comap_maximalIdeal, gaussianField5MinusPlace_maximalIdeal]
  change gaussianField5Minus.under (NumberField.RingOfIntegers ℚ) =
    concreteFivePlace.maximalIdeal.asIdeal
  rw [gaussianField5Minus_under_rational, concreteFivePlace_maximalIdeal,
    concreteFiveHeightOne_asIdeal_eq_span]

/-- The base-changed concrete split curve has split multiplicative reduction
at the Gaussian place cut out by (2 + i). -/
theorem gaussianField5PlusPlace_hasSplitMultiplicativeReductionAt :
    (concreteSplitPuncturedCurve.baseChange GaussianField).HasSplitMultiplicativeReductionAt
      gaussianField5PlusPlace := by
  refine PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_baseChange
    (X := concreteSplitPuncturedCurve) (place := gaussianField5PlusPlace) ?_
  rw [gaussianField5PlusPlace_comap]
  exact concreteSplitPuncturedCurve_hasSplitMultiplicativeReductionAt_five

/-- The base-changed concrete split curve has split multiplicative reduction
at the Gaussian place cut out by (2 - i). -/
theorem gaussianField5MinusPlace_hasSplitMultiplicativeReductionAt :
    (concreteSplitPuncturedCurve.baseChange GaussianField).HasSplitMultiplicativeReductionAt
      gaussianField5MinusPlace := by
  refine PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_baseChange
    (X := concreteSplitPuncturedCurve) (place := gaussianField5MinusPlace) ?_
  rw [gaussianField5MinusPlace_comap]
  exact concreteSplitPuncturedCurve_hasSplitMultiplicativeReductionAt_five

/-- The base-changed concrete split curve has multiplicative reduction at the
Gaussian place cut out by (2 + i). -/
theorem gaussianField5PlusPlace_hasMultiplicativeReductionAt :
    (concreteSplitPuncturedCurve.baseChange GaussianField).HasMultiplicativeReductionAt
      gaussianField5PlusPlace :=
  PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_imp_multiplicative
    gaussianField5PlusPlace_hasSplitMultiplicativeReductionAt

/-- The base-changed concrete split curve has multiplicative reduction at the
Gaussian place cut out by (2 - i). -/
theorem gaussianField5MinusPlace_hasMultiplicativeReductionAt :
    (concreteSplitPuncturedCurve.baseChange GaussianField).HasMultiplicativeReductionAt
      gaussianField5MinusPlace :=
  PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_imp_multiplicative
    gaussianField5MinusPlace_hasSplitMultiplicativeReductionAt

#print axioms gaussianInt5Plus_norm
#print axioms gaussianInt5Plus_mul_minus
#print axioms gaussianInt5Plus_irreducible
#print axioms gaussianInt5Minus_irreducible
#print axioms gaussianInt5Plus_span_isMaximal
#print axioms gaussianInt5Minus_span_isMaximal
#print axioms gaussianInt5PlusResidueMap_ker
#print axioms gaussianInt5PlusResidueEquiv
#print axioms gaussianInt5Plus_cardQuot
#print axioms gaussianInt5Plus_absNorm
#print axioms gaussianInt5Minus_absNorm
#print axioms gaussianInt5Plus_ne_minus_span
#print axioms gaussianField5Plus_ne_minus
#print axioms gaussianField5PlusPlace_ne_minusPlace
#print axioms gaussianField5Plus_eq_map
#print axioms gaussianField5Plus_absNorm
#print axioms gaussianField5Minus_absNorm
#print axioms gaussianField5PlusPlace_residueCharacteristic
#print axioms gaussianField5MinusPlace_residueCharacteristic
#print axioms gaussianField5PlusPlace_residueCharacteristic_odd
#print axioms gaussianField5MinusPlace_residueCharacteristic_odd
#print axioms gaussianField5PlusPlace_comap
#print axioms gaussianField5MinusPlace_comap
#print axioms gaussianField5PlusPlace_hasSplitMultiplicativeReductionAt
#print axioms gaussianField5MinusPlace_hasSplitMultiplicativeReductionAt

end LeanFormal.IUT.XiFPaper.S2705GaussianFivePlacesActual
end
