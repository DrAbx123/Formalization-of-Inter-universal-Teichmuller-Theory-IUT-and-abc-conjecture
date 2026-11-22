import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianIntegralBasis
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import tmp.sheaf.xif.paper.S2687Split2161Actual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

/-!
# S2701: the Gaussian prime ideals above 2161

The Gaussian integers Z[i] contain the two explicit elements
15 + 44i and 15 - 44i, both of norm 2161 = 15^2 + 44^2.  Since 2161
is prime, both elements are irreducible, so the principal ideals they
generate are maximal in the Euclidean domain Z[i].

The two maximal ideals are then mapped along the actual ring-of-integers
equivalence GaussianInt = NumberField.RingOfIntegers GaussianField and
give two finite places of the Gaussian field.  Their residue fields are
identified with ZMod 2161, hence both residue characteristics are 2161
(and odd).

The proof is complete: no proof holes and no extra axioms.
-/

namespace LeanFormal.IUT.XiFPaper.S2701GaussianPrimeIdealsActual

local instance s2701GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s2701Fact2161 : Fact (Nat.Prime 2161) := ⟨by decide⟩

/-- The ring of integers of the Gaussian field. -/
abbrev GaussianO : Type := NumberField.RingOfIntegers GaussianField

/-! ## 1. The two Gaussian integers of norm 2161 -/

/-- The Gaussian integer 15 + 44i. -/
def gaussianInt2161Plus : GaussianInt := ⟨15, 44⟩

/-- The Gaussian integer 15 - 44i. -/
def gaussianInt2161Minus : GaussianInt := ⟨15, -44⟩

/-- The norm of 15 + 44i is 2161 = 15^2 + 44^2. -/
theorem gaussianInt2161Plus_norm :
    Zsqrtd.norm gaussianInt2161Plus = 2161 := by
  simp [gaussianInt2161Plus, Zsqrtd.norm_def]

/-- The norm of 15 - 44i is 2161 = 15^2 + 44^2. -/
theorem gaussianInt2161Minus_norm :
    Zsqrtd.norm gaussianInt2161Minus = 2161 := by
  simp [gaussianInt2161Minus, Zsqrtd.norm_def]

/-- The actual factorization (15 + 44i)(15 - 44i) = 2161. -/
theorem gaussianInt2161Plus_mul_minus :
    gaussianInt2161Plus * gaussianInt2161Minus = (2161 : GaussianInt) := by
  apply Zsqrtd.ext_iff.mpr
  constructor <;> norm_num [gaussianInt2161Plus, gaussianInt2161Minus]

/-- The principal-ideal factorization (2161) = (15+44i)(15-44i). -/
theorem gaussianInt2161_ideal_factorization :
    Ideal.span {(2161 : GaussianInt)} =
      Ideal.span {gaussianInt2161Plus} * Ideal.span {gaussianInt2161Minus} := by
  rw [← gaussianInt2161Plus_mul_minus]
  exact (Ideal.span_singleton_mul_span_singleton _ _).symm

/-- 2161 lies in the ideal (15 + 44i). -/
theorem gaussianInt2161_mem_plus :
    (2161 : GaussianInt) ∈ Ideal.span {gaussianInt2161Plus} := by
  rw [← gaussianInt2161Plus_mul_minus]
  exact Ideal.mul_mem_right gaussianInt2161Minus _
    (Ideal.subset_span (Set.mem_singleton_iff.mpr rfl))

/-- 2161 lies in the ideal (15 - 44i). -/
theorem gaussianInt2161_mem_minus :
    (2161 : GaussianInt) ∈ Ideal.span {gaussianInt2161Minus} := by
  rw [Ideal.mem_span_singleton]
  exact ⟨gaussianInt2161Plus, by
    rw [mul_comm, gaussianInt2161Plus_mul_minus]⟩

/-! ## 2. Irreducibility and maximality in Z[i] -/

/-- 15 + 44i is irreducible: its norm is the prime 2161. -/
theorem gaussianInt2161Plus_irreducible : Irreducible gaussianInt2161Plus := by
  rw [irreducible_iff]
  constructor
  · intro hunit
    have hnorm : (Zsqrtd.norm gaussianInt2161Plus).natAbs = 1 :=
      Zsqrtd.norm_eq_one_iff.mpr hunit
    rw [gaussianInt2161Plus_norm] at hnorm
    norm_num at hnorm
  · intro a b hab
    have hnorm : (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs = 2161 := by
      calc (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs
          = (Zsqrtd.norm (a * b)).natAbs := by rw [Zsqrtd.norm_mul, Int.natAbs_mul]
        _ = (Zsqrtd.norm gaussianInt2161Plus).natAbs := by rw [hab]
        _ = 2161 := by rw [gaussianInt2161Plus_norm]; norm_num
    have hdvd : (Zsqrtd.norm a).natAbs ∣ 2161 := ⟨(Zsqrtd.norm b).natAbs, hnorm.symm⟩
    have hcases := s2701Fact2161.out.eq_one_or_self_of_dvd
      ((Zsqrtd.norm a).natAbs) hdvd
    rcases hcases with ha | ha
    · left
      exact Zsqrtd.norm_eq_one_iff.mp ha
    · right
      have hb : (Zsqrtd.norm b).natAbs = 1 := by
        rw [ha] at hnorm
        omega
      exact Zsqrtd.norm_eq_one_iff.mp hb

/-- 15 - 44i is irreducible: its norm is the prime 2161. -/
theorem gaussianInt2161Minus_irreducible : Irreducible gaussianInt2161Minus := by
  rw [irreducible_iff]
  constructor
  · intro hunit
    have hnorm : (Zsqrtd.norm gaussianInt2161Minus).natAbs = 1 :=
      Zsqrtd.norm_eq_one_iff.mpr hunit
    rw [gaussianInt2161Minus_norm] at hnorm
    norm_num at hnorm
  · intro a b hab
    have hnorm : (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs = 2161 := by
      calc (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs
          = (Zsqrtd.norm (a * b)).natAbs := by rw [Zsqrtd.norm_mul, Int.natAbs_mul]
        _ = (Zsqrtd.norm gaussianInt2161Minus).natAbs := by rw [hab]
        _ = 2161 := by rw [gaussianInt2161Minus_norm]; norm_num
    have hdvd : (Zsqrtd.norm a).natAbs ∣ 2161 := ⟨(Zsqrtd.norm b).natAbs, hnorm.symm⟩
    have hcases := s2701Fact2161.out.eq_one_or_self_of_dvd
      ((Zsqrtd.norm a).natAbs) hdvd
    rcases hcases with ha | ha
    · left
      exact Zsqrtd.norm_eq_one_iff.mp ha
    · right
      have hb : (Zsqrtd.norm b).natAbs = 1 := by
        rw [ha] at hnorm
        omega
      exact Zsqrtd.norm_eq_one_iff.mp hb

/-- The principal ideal (15 + 44i) is maximal in Z[i]. -/
theorem gaussianInt2161Plus_span_isMaximal :
    (Ideal.span {gaussianInt2161Plus}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible gaussianInt2161Plus_irreducible

instance gaussianInt2161Plus_span_isMaximal_instance :
    (Ideal.span {gaussianInt2161Plus}).IsMaximal :=
  gaussianInt2161Plus_span_isMaximal

/-- The principal ideal (15 - 44i) is maximal in Z[i]. -/
theorem gaussianInt2161Minus_span_isMaximal :
    (Ideal.span {gaussianInt2161Minus}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible gaussianInt2161Minus_irreducible

instance gaussianInt2161Minus_span_isMaximal_instance :
    (Ideal.span {gaussianInt2161Minus}).IsMaximal :=
  gaussianInt2161Minus_span_isMaximal

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

/-! ## 3. Explicit residue maps Z[i] -> ZMod 2161

We have 147^2 = -1 and 15 + 44*147 = 0 modulo 2161, and
2014^2 = -1 with 15 - 44*2014 = 0 modulo 2161.  Hence the two
residue maps below kill 15 + 44i and 15 - 44i respectively. -/

/-- The residue map Z[i] -> ZMod 2161 sending i to 147. -/
noncomputable def gaussianInt2161PlusResidueMap : GaussianInt →+* ZMod 2161 :=
  Zsqrtd.lift ⟨(147 : ZMod 2161), by decide⟩

/-- The residue map Z[i] -> ZMod 2161 sending i to 2014 = -147. -/
noncomputable def gaussianInt2161MinusResidueMap : GaussianInt →+* ZMod 2161 :=
  Zsqrtd.lift ⟨(2014 : ZMod 2161), by decide⟩

/-- The plus residue map kills 15 + 44i. -/
theorem gaussianInt2161PlusResidueMap_generator :
    gaussianInt2161PlusResidueMap gaussianInt2161Plus = 0 := by
  simp [gaussianInt2161PlusResidueMap, gaussianInt2161Plus]
  decide

/-- The minus residue map kills 15 - 44i. -/
theorem gaussianInt2161MinusResidueMap_generator :
    gaussianInt2161MinusResidueMap gaussianInt2161Minus = 0 := by
  simp [gaussianInt2161MinusResidueMap, gaussianInt2161Minus]
  decide

/-- The plus residue map is surjective, already on the integer classes. -/
theorem gaussianInt2161PlusResidueMap_surjective :
    Function.Surjective gaussianInt2161PlusResidueMap := by
  intro y
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective y
  refine ⟨(a : GaussianInt), ?_⟩
  simp [gaussianInt2161PlusResidueMap]

/-- The minus residue map is surjective, already on the integer classes. -/
theorem gaussianInt2161MinusResidueMap_surjective :
    Function.Surjective gaussianInt2161MinusResidueMap := by
  intro y
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective y
  refine ⟨(a : GaussianInt), ?_⟩
  simp [gaussianInt2161MinusResidueMap]

/-- The ideal (15 + 44i) is contained in the kernel of the plus residue map. -/
theorem gaussianInt2161Plus_ideal_le_ker :
    Ideal.span {gaussianInt2161Plus} ≤
      RingHom.ker gaussianInt2161PlusResidueMap := by
  refine Ideal.span_le.mpr ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact (RingHom.mem_ker).mpr gaussianInt2161PlusResidueMap_generator

/-- The ideal (15 - 44i) is contained in the kernel of the minus residue map. -/
theorem gaussianInt2161Minus_ideal_le_ker :
    Ideal.span {gaussianInt2161Minus} ≤
      RingHom.ker gaussianInt2161MinusResidueMap := by
  refine Ideal.span_le.mpr ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact (RingHom.mem_ker).mpr gaussianInt2161MinusResidueMap_generator

/-- The kernel of the plus residue map is exactly (15 + 44i). -/
theorem gaussianInt2161PlusResidueMap_ker :
    RingHom.ker gaussianInt2161PlusResidueMap =
      Ideal.span {gaussianInt2161Plus} := by
  have hker : (RingHom.ker gaussianInt2161PlusResidueMap).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective gaussianInt2161PlusResidueMap
      gaussianInt2161PlusResidueMap_surjective
  exact (Ideal.IsMaximal.eq_of_le gaussianInt2161Plus_span_isMaximal hker.ne_top
    gaussianInt2161Plus_ideal_le_ker).symm

/-- The kernel of the minus residue map is exactly (15 - 44i). -/
theorem gaussianInt2161MinusResidueMap_ker :
    RingHom.ker gaussianInt2161MinusResidueMap =
      Ideal.span {gaussianInt2161Minus} := by
  have hker : (RingHom.ker gaussianInt2161MinusResidueMap).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective gaussianInt2161MinusResidueMap
      gaussianInt2161MinusResidueMap_surjective
  exact (Ideal.IsMaximal.eq_of_le gaussianInt2161Minus_span_isMaximal hker.ne_top
    gaussianInt2161Minus_ideal_le_ker).symm

/-- The two principal ideals are distinct: the plus residue map sends
15 - 44i to 30, which is nonzero modulo 2161. -/
theorem gaussianInt2161Plus_ne_minus_span :
    Ideal.span {gaussianInt2161Plus} ≠ Ideal.span {gaussianInt2161Minus} := by
  intro h
  have hmem : gaussianInt2161Minus ∈ Ideal.span {gaussianInt2161Plus} := by
    rw [h]
    exact Ideal.subset_span (Set.mem_singleton_iff.mpr rfl)
  have hker : gaussianInt2161Minus ∈ RingHom.ker gaussianInt2161PlusResidueMap :=
    gaussianInt2161Plus_ideal_le_ker hmem
  have hzero : gaussianInt2161PlusResidueMap gaussianInt2161Minus = 0 := hker
  have h30 : gaussianInt2161PlusResidueMap gaussianInt2161Minus = 30 := by
    simp [gaussianInt2161PlusResidueMap, gaussianInt2161Minus]
    decide
  rw [h30] at hzero
  exact (by decide : (30 : ZMod 2161) ≠ 0) hzero

/-- The residue quotient Z[i]/(15+44i) is ZMod 2161. -/
noncomputable def gaussianInt2161PlusResidueEquiv :
    (GaussianInt ⧸ Ideal.span {gaussianInt2161Plus}) ≃+* ZMod 2161 :=
  (Ideal.quotEquivOfEq gaussianInt2161PlusResidueMap_ker.symm).trans
    (RingHom.quotientKerEquivOfSurjective gaussianInt2161PlusResidueMap_surjective)

/-- The residue quotient Z[i]/(15-44i) is ZMod 2161. -/
noncomputable def gaussianInt2161MinusResidueEquiv :
    (GaussianInt ⧸ Ideal.span {gaussianInt2161Minus}) ≃+* ZMod 2161 :=
  (Ideal.quotEquivOfEq gaussianInt2161MinusResidueMap_ker.symm).trans
    (RingHom.quotientKerEquivOfSurjective gaussianInt2161MinusResidueMap_surjective)

/-- The quotient Z[i]/(15+44i) has 2161 elements. -/
theorem gaussianInt2161Plus_cardQuot :
    Nat.card (GaussianInt ⧸ Ideal.span {gaussianInt2161Plus}) = 2161 := by
  calc Nat.card (GaussianInt ⧸ Ideal.span {gaussianInt2161Plus})
      = Nat.card (ZMod 2161) :=
        Nat.card_congr gaussianInt2161PlusResidueEquiv.toEquiv
    _ = 2161 := Nat.card_zmod 2161

/-- The quotient Z[i]/(15-44i) has 2161 elements. -/
theorem gaussianInt2161Minus_cardQuot :
    Nat.card (GaussianInt ⧸ Ideal.span {gaussianInt2161Minus}) = 2161 := by
  calc Nat.card (GaussianInt ⧸ Ideal.span {gaussianInt2161Minus})
      = Nat.card (ZMod 2161) :=
        Nat.card_congr gaussianInt2161MinusResidueEquiv.toEquiv
    _ = 2161 := Nat.card_zmod 2161

/-- The absolute norm of the principal ideal (15+44i) in Z[i] is 2161. -/
theorem gaussianInt2161Plus_absNorm :
    Ideal.absNorm (Ideal.span {gaussianInt2161Plus}) = 2161 := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact gaussianInt2161Plus_cardQuot

/-- The absolute norm of the principal ideal (15-44i) in Z[i] is 2161. -/
theorem gaussianInt2161Minus_absNorm :
    Ideal.absNorm (Ideal.span {gaussianInt2161Minus}) = 2161 := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact gaussianInt2161Minus_cardQuot

/-! ## 4. The corresponding ideals of the ring of integers -/

/-- The prime ideal of the ring of integers of the Gaussian field
corresponding to (15 + 44i). -/
noncomputable def gaussianField2161Plus : Ideal GaussianO :=
  Ideal.comap gaussianRingOfIntegersEquivGaussianInt.toRingHom
    (Ideal.span {gaussianInt2161Plus})

/-- The prime ideal of the ring of integers corresponding to (15 - 44i). -/
noncomputable def gaussianField2161Minus : Ideal GaussianO :=
  Ideal.comap gaussianRingOfIntegersEquivGaussianInt.toRingHom
    (Ideal.span {gaussianInt2161Minus})

/-- The image of (15+44i) under the actual ring-of-integers equivalence. -/
theorem gaussianField2161Plus_eq_map :
    gaussianField2161Plus =
      Ideal.map gaussianIntEquivRingOfIntegers.toRingHom
        (Ideal.span {gaussianInt2161Plus}) := by
  rw [gaussianField2161Plus]
  exact (Ideal.map_symm (f := gaussianRingOfIntegersEquivGaussianInt)).symm

/-- The image of (15-44i) under the actual ring-of-integers equivalence. -/
theorem gaussianField2161Minus_eq_map :
    gaussianField2161Minus =
      Ideal.map gaussianIntEquivRingOfIntegers.toRingHom
        (Ideal.span {gaussianInt2161Minus}) := by
  rw [gaussianField2161Minus]
  exact (Ideal.map_symm (f := gaussianRingOfIntegersEquivGaussianInt)).symm

/-- The transported plus ideal is maximal. -/
instance gaussianField2161Plus_isMaximal : gaussianField2161Plus.IsMaximal :=
  Ideal.comap_isMaximal_of_equiv gaussianRingOfIntegersEquivGaussianInt

/-- The transported minus ideal is maximal. -/
instance gaussianField2161Minus_isMaximal : gaussianField2161Minus.IsMaximal :=
  Ideal.comap_isMaximal_of_equiv gaussianRingOfIntegersEquivGaussianInt

/-- The two transported ideals are distinct. -/
theorem gaussianField2161Plus_ne_minus :
    gaussianField2161Plus ≠ gaussianField2161Minus := by
  intro h
  have hmap := congrArg
    (Ideal.map gaussianRingOfIntegersEquivGaussianInt.toRingHom) h
  rw [gaussianField2161Plus, gaussianField2161Minus,
    Ideal.map_comap_of_surjective
      gaussianRingOfIntegersEquivGaussianInt.toRingHom
      gaussianRingOfIntegersEquivGaussianInt.surjective,
    Ideal.map_comap_of_surjective
      gaussianRingOfIntegersEquivGaussianInt.toRingHom
      gaussianRingOfIntegersEquivGaussianInt.surjective] at hmap
  exact gaussianInt2161Plus_ne_minus_span hmap

/-- The residue quotient of the transported plus ideal is ZMod 2161. -/
noncomputable def gaussianField2161PlusResidueEquiv :
    (GaussianO ⧸ gaussianField2161Plus) ≃+* ZMod 2161 :=
  (Ideal.quotientEquiv (gaussianField2161Plus)
    (Ideal.span {gaussianInt2161Plus})
    gaussianRingOfIntegersEquivGaussianInt
    (by
      change Ideal.span {gaussianInt2161Plus} =
        Ideal.map gaussianRingOfIntegersEquivGaussianInt.toRingHom
          gaussianField2161Plus
      rw [gaussianField2161Plus,
        Ideal.map_comap_of_surjective
          gaussianRingOfIntegersEquivGaussianInt.toRingHom
          gaussianRingOfIntegersEquivGaussianInt.surjective])).trans
    gaussianInt2161PlusResidueEquiv

/-- The residue quotient of the transported minus ideal is ZMod 2161. -/
noncomputable def gaussianField2161MinusResidueEquiv :
    (GaussianO ⧸ gaussianField2161Minus) ≃+* ZMod 2161 :=
  (Ideal.quotientEquiv (gaussianField2161Minus)
    (Ideal.span {gaussianInt2161Minus})
    gaussianRingOfIntegersEquivGaussianInt
    (by
      change Ideal.span {gaussianInt2161Minus} =
        Ideal.map gaussianRingOfIntegersEquivGaussianInt.toRingHom
          gaussianField2161Minus
      rw [gaussianField2161Minus,
        Ideal.map_comap_of_surjective
          gaussianRingOfIntegersEquivGaussianInt.toRingHom
          gaussianRingOfIntegersEquivGaussianInt.surjective])).trans
    gaussianInt2161MinusResidueEquiv

/-- The absolute norm of the transported plus ideal is 2161. -/
theorem gaussianField2161Plus_absNorm :
    Ideal.absNorm gaussianField2161Plus = 2161 := by
  rw [Ideal.absNorm_apply]
  rw [Submodule.cardQuot_apply]
  calc Nat.card (GaussianO ⧸ gaussianField2161Plus)
      = Nat.card (ZMod 2161) :=
        Nat.card_congr gaussianField2161PlusResidueEquiv.toEquiv
    _ = 2161 := Nat.card_zmod 2161

/-- The absolute norm of the transported minus ideal is 2161. -/
theorem gaussianField2161Minus_absNorm :
    Ideal.absNorm gaussianField2161Minus = 2161 := by
  rw [Ideal.absNorm_apply]
  rw [Submodule.cardQuot_apply]
  calc Nat.card (GaussianO ⧸ gaussianField2161Minus)
      = Nat.card (ZMod 2161) :=
        Nat.card_congr gaussianField2161MinusResidueEquiv.toEquiv
    _ = 2161 := Nat.card_zmod 2161

/-! ## 5. The two finite places and their residue characteristics -/

/-- The finite place of the Gaussian field at (15 + 44i). -/
noncomputable def gaussianField2161PlusPlace : NumberField.FinitePlace GaussianField :=
  NumberField.FinitePlace.mk
    { asIdeal := gaussianField2161Plus
      isPrime := gaussianField2161Plus_isMaximal.isPrime
      ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField
        gaussianField2161Plus_isMaximal
        (NumberField.RingOfIntegers.not_isField GaussianField) }

/-- The finite place of the Gaussian field at (15 - 44i). -/
noncomputable def gaussianField2161MinusPlace : NumberField.FinitePlace GaussianField :=
  NumberField.FinitePlace.mk
    { asIdeal := gaussianField2161Minus
      isPrime := gaussianField2161Minus_isMaximal.isPrime
      ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField
        gaussianField2161Minus_isMaximal
        (NumberField.RingOfIntegers.not_isField GaussianField) }

/-- The maximal ideal of the plus place is the transported plus ideal. -/
theorem gaussianField2161PlusPlace_maximalIdeal :
    gaussianField2161PlusPlace.maximalIdeal.asIdeal = gaussianField2161Plus :=
  congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
    (NumberField.FinitePlace.maximalIdeal_mk _)

/-- The maximal ideal of the minus place is the transported minus ideal. -/
theorem gaussianField2161MinusPlace_maximalIdeal :
    gaussianField2161MinusPlace.maximalIdeal.asIdeal = gaussianField2161Minus :=
  congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
    (NumberField.FinitePlace.maximalIdeal_mk _)

/-- The two finite places are distinct. -/
theorem gaussianField2161PlusPlace_ne_minusPlace :
    gaussianField2161PlusPlace ≠ gaussianField2161MinusPlace := by
  intro h
  have hmax := congrArg NumberField.FinitePlace.maximalIdeal h
  have hasIdeal := congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hmax
  rw [gaussianField2161PlusPlace_maximalIdeal,
    gaussianField2161MinusPlace_maximalIdeal] at hasIdeal
  exact gaussianField2161Plus_ne_minus hasIdeal

/-- The residue characteristic of the plus place is 2161. -/
theorem gaussianField2161PlusPlace_residueCharacteristic :
    NumberFieldFinitePlace.residueCharacteristic gaussianField2161PlusPlace = 2161 := by
  rw [NumberFieldFinitePlace.residueCharacteristic]
  change ringChar (GaussianO ⧸ gaussianField2161PlusPlace.maximalIdeal.asIdeal) = 2161
  rw [gaussianField2161PlusPlace_maximalIdeal]
  rw [ringChar.eq_iff]
  exact (RingHom.charP_iff
    (gaussianField2161PlusResidueEquiv :
      (GaussianO ⧸ gaussianField2161Plus) →+* ZMod 2161)
    gaussianField2161PlusResidueEquiv.injective 2161).mpr inferInstance

/-- The residue characteristic of the minus place is 2161. -/
theorem gaussianField2161MinusPlace_residueCharacteristic :
    NumberFieldFinitePlace.residueCharacteristic gaussianField2161MinusPlace = 2161 := by
  rw [NumberFieldFinitePlace.residueCharacteristic]
  change ringChar (GaussianO ⧸ gaussianField2161MinusPlace.maximalIdeal.asIdeal) = 2161
  rw [gaussianField2161MinusPlace_maximalIdeal]
  rw [ringChar.eq_iff]
  exact (RingHom.charP_iff
    (gaussianField2161MinusResidueEquiv :
      (GaussianO ⧸ gaussianField2161Minus) →+* ZMod 2161)
    gaussianField2161MinusResidueEquiv.injective 2161).mpr inferInstance

/-- The residue characteristic of the plus place is odd. -/
theorem gaussianField2161PlusPlace_residueCharacteristic_odd :
    Odd (NumberFieldFinitePlace.residueCharacteristic gaussianField2161PlusPlace) := by
  rw [gaussianField2161PlusPlace_residueCharacteristic]
  exact ⟨1080, by norm_num⟩

/-- The residue characteristic of the minus place is odd. -/
theorem gaussianField2161MinusPlace_residueCharacteristic_odd :
    Odd (NumberFieldFinitePlace.residueCharacteristic gaussianField2161MinusPlace) := by
  rw [gaussianField2161MinusPlace_residueCharacteristic]
  exact ⟨1080, by norm_num⟩


/-! ## 6. The places over the rational prime 2161 and split multiplicative reduction -/

/-- The height-one prime of the rational ring of integers at 2161 is the
principal ideal generated by 2161. -/
theorem concrete2161HeightOne_asIdeal_eq_span :
    concrete2161HeightOne.asIdeal =
      Ideal.span {(2161 : NumberField.RingOfIntegers ℚ)} := by
  let e : NumberField.RingOfIntegers ℚ ≃+* ℤ :=
    Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)
  have h := Rat.HeightOneSpectrum.span_natGenerator
    (R := NumberField.RingOfIntegers ℚ) concrete2161HeightOne
  rw [concrete2161HeightOne_natGenerator] at h
  change Ideal.span {(2161 : ℤ)} =
    Ideal.map e.toRingHom concrete2161HeightOne.asIdeal at h
  have h' := congrArg (Ideal.map e.symm.toRingHom) h
  rw [Ideal.map_span] at h'
  simp only [Set.image_singleton] at h'
  simp at h'
  exact h'.symm

/-- 2161 lies in the transported plus ideal. -/
theorem gaussianField2161Plus_mem_natCast :
    (2161 : GaussianO) ∈ gaussianField2161Plus := by
  rw [gaussianField2161Plus, Ideal.mem_comap]
  have h : gaussianRingOfIntegersEquivGaussianInt.toRingHom (2161 : GaussianO) =
      (2161 : GaussianInt) := map_natCast _ 2161
  rw [h]
  exact gaussianInt2161_mem_plus

/-- 2161 lies in the transported minus ideal. -/
theorem gaussianField2161Minus_mem_natCast :
    (2161 : GaussianO) ∈ gaussianField2161Minus := by
  rw [gaussianField2161Minus, Ideal.mem_comap]
  have h : gaussianRingOfIntegersEquivGaussianInt.toRingHom (2161 : GaussianO) =
      (2161 : GaussianInt) := map_natCast _ 2161
  rw [h]
  exact gaussianInt2161_mem_minus

/-- The transported plus ideal lies over the rational prime ideal (2161). -/
theorem gaussianField2161Plus_under_rational :
    gaussianField2161Plus.under (NumberField.RingOfIntegers ℚ) =
      Ideal.span {(2161 : NumberField.RingOfIntegers ℚ)} := by
  have hle : Ideal.span {(2161 : NumberField.RingOfIntegers ℚ)} ≤
      gaussianField2161Plus.under (NumberField.RingOfIntegers ℚ) := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    change (2161 : NumberField.RingOfIntegers ℚ) ∈
      Ideal.comap (algebraMap (NumberField.RingOfIntegers ℚ) GaussianO)
        gaussianField2161Plus
    rw [Ideal.mem_comap]
    have h : algebraMap (NumberField.RingOfIntegers ℚ) GaussianO
        (2161 : NumberField.RingOfIntegers ℚ) = (2161 : GaussianO) :=
      map_natCast _ 2161
    rw [h]
    exact gaussianField2161Plus_mem_natCast
  have hne : gaussianField2161Plus.under (NumberField.RingOfIntegers ℚ) ≠ ⊤ := by
    intro h
    have h1 : (1 : NumberField.RingOfIntegers ℚ) ∈
        gaussianField2161Plus.under (NumberField.RingOfIntegers ℚ) := by
      rw [h]; exact Submodule.mem_top
    change (1 : NumberField.RingOfIntegers ℚ) ∈
      Ideal.comap (algebraMap (NumberField.RingOfIntegers ℚ) GaussianO)
        gaussianField2161Plus at h1
    rw [Ideal.mem_comap] at h1
    have hone : (1 : GaussianO) ∈ gaussianField2161Plus := by
      simpa using h1
    have htop : (⊤ : Ideal GaussianO) ≤ gaussianField2161Plus := by
      rw [top_le_iff, Ideal.eq_top_iff_one]
      exact hone
    exact gaussianField2161Plus_isMaximal.ne_top (top_le_iff.mp htop)
  have hmax : (Ideal.span {(2161 : NumberField.RingOfIntegers ℚ)}).IsMaximal := by
    rw [← concrete2161HeightOne_asIdeal_eq_span]
    exact concrete2161HeightOne.isPrime.isMaximal concrete2161HeightOne.ne_bot
  exact (Ideal.IsMaximal.eq_of_le hmax hne hle).symm

/-- The transported minus ideal lies over the rational prime ideal (2161). -/
theorem gaussianField2161Minus_under_rational :
    gaussianField2161Minus.under (NumberField.RingOfIntegers ℚ) =
      Ideal.span {(2161 : NumberField.RingOfIntegers ℚ)} := by
  have hle : Ideal.span {(2161 : NumberField.RingOfIntegers ℚ)} ≤
      gaussianField2161Minus.under (NumberField.RingOfIntegers ℚ) := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    change (2161 : NumberField.RingOfIntegers ℚ) ∈
      Ideal.comap (algebraMap (NumberField.RingOfIntegers ℚ) GaussianO)
        gaussianField2161Minus
    rw [Ideal.mem_comap]
    have h : algebraMap (NumberField.RingOfIntegers ℚ) GaussianO
        (2161 : NumberField.RingOfIntegers ℚ) = (2161 : GaussianO) :=
      map_natCast _ 2161
    rw [h]
    exact gaussianField2161Minus_mem_natCast
  have hne : gaussianField2161Minus.under (NumberField.RingOfIntegers ℚ) ≠ ⊤ := by
    intro h
    have h1 : (1 : NumberField.RingOfIntegers ℚ) ∈
        gaussianField2161Minus.under (NumberField.RingOfIntegers ℚ) := by
      rw [h]; exact Submodule.mem_top
    change (1 : NumberField.RingOfIntegers ℚ) ∈
      Ideal.comap (algebraMap (NumberField.RingOfIntegers ℚ) GaussianO)
        gaussianField2161Minus at h1
    rw [Ideal.mem_comap] at h1
    have hone : (1 : GaussianO) ∈ gaussianField2161Minus := by
      simpa using h1
    have htop : (⊤ : Ideal GaussianO) ≤ gaussianField2161Minus := by
      rw [top_le_iff, Ideal.eq_top_iff_one]
      exact hone
    exact gaussianField2161Minus_isMaximal.ne_top (top_le_iff.mp htop)
  have hmax : (Ideal.span {(2161 : NumberField.RingOfIntegers ℚ)}).IsMaximal := by
    rw [← concrete2161HeightOne_asIdeal_eq_span]
    exact concrete2161HeightOne.isPrime.isMaximal concrete2161HeightOne.ne_bot
  exact (Ideal.IsMaximal.eq_of_le hmax hne hle).symm

/-- The plus place restricts to the rational place at 2161. -/
theorem gaussianField2161PlusPlace_comap :
    NumberFieldFinitePlace.comap (k := ℚ) gaussianField2161PlusPlace = S2687Place := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NumberFieldFinitePlace.comap_maximalIdeal, gaussianField2161PlusPlace_maximalIdeal]
  change gaussianField2161Plus.under (NumberField.RingOfIntegers ℚ) =
    S2687Place.maximalIdeal.asIdeal
  rw [gaussianField2161Plus_under_rational, S2687Place_maximalIdeal,
    concrete2161HeightOne_asIdeal_eq_span]

/-- The minus place restricts to the rational place at 2161. -/
theorem gaussianField2161MinusPlace_comap :
    NumberFieldFinitePlace.comap (k := ℚ) gaussianField2161MinusPlace = S2687Place := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NumberFieldFinitePlace.comap_maximalIdeal, gaussianField2161MinusPlace_maximalIdeal]
  change gaussianField2161Minus.under (NumberField.RingOfIntegers ℚ) =
    S2687Place.maximalIdeal.asIdeal
  rw [gaussianField2161Minus_under_rational, S2687Place_maximalIdeal,
    concrete2161HeightOne_asIdeal_eq_span]

/-- The base-changed concrete split curve has split multiplicative reduction
at the Gaussian place cut out by (15 + 44i). -/
theorem gaussianField2161PlusPlace_hasSplitMultiplicativeReductionAt :
    (concreteSplitPuncturedCurve.baseChange GaussianField).HasSplitMultiplicativeReductionAt
      gaussianField2161PlusPlace := by
  refine PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_baseChange
    (X := concreteSplitPuncturedCurve) (place := gaussianField2161PlusPlace) ?_
  rw [gaussianField2161PlusPlace_comap]
  exact S2687HasSplitMultiplicativeReductionAt2161

/-- The base-changed concrete split curve has split multiplicative reduction
at the Gaussian place cut out by (15 - 44i). -/
theorem gaussianField2161MinusPlace_hasSplitMultiplicativeReductionAt :
    (concreteSplitPuncturedCurve.baseChange GaussianField).HasSplitMultiplicativeReductionAt
      gaussianField2161MinusPlace := by
  refine PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_baseChange
    (X := concreteSplitPuncturedCurve) (place := gaussianField2161MinusPlace) ?_
  rw [gaussianField2161MinusPlace_comap]
  exact S2687HasSplitMultiplicativeReductionAt2161

/-- The base-changed concrete split curve has multiplicative reduction at the
Gaussian place cut out by (15 + 44i). -/
theorem gaussianField2161PlusPlace_hasMultiplicativeReductionAt :
    (concreteSplitPuncturedCurve.baseChange GaussianField).HasMultiplicativeReductionAt
      gaussianField2161PlusPlace :=
  PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_imp_multiplicative
    gaussianField2161PlusPlace_hasSplitMultiplicativeReductionAt

/-- The base-changed concrete split curve has multiplicative reduction at the
Gaussian place cut out by (15 - 44i). -/
theorem gaussianField2161MinusPlace_hasMultiplicativeReductionAt :
    (concreteSplitPuncturedCurve.baseChange GaussianField).HasMultiplicativeReductionAt
      gaussianField2161MinusPlace :=
  PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_imp_multiplicative
    gaussianField2161MinusPlace_hasSplitMultiplicativeReductionAt

#print axioms gaussianInt2161Plus_norm
#print axioms gaussianInt2161Plus_mul_minus
#print axioms gaussianInt2161Plus_irreducible
#print axioms gaussianInt2161Minus_irreducible
#print axioms gaussianInt2161Plus_span_isMaximal
#print axioms gaussianInt2161Minus_span_isMaximal
#print axioms gaussianInt2161PlusResidueMap_ker
#print axioms gaussianInt2161PlusResidueEquiv
#print axioms gaussianInt2161Plus_cardQuot
#print axioms gaussianInt2161Plus_absNorm
#print axioms gaussianInt2161Minus_absNorm
#print axioms gaussianInt2161Plus_ne_minus_span
#print axioms gaussianField2161Plus_ne_minus
#print axioms gaussianField2161PlusPlace_ne_minusPlace
#print axioms gaussianField2161Plus_eq_map
#print axioms gaussianField2161Plus_absNorm
#print axioms gaussianField2161Minus_absNorm
#print axioms gaussianField2161PlusPlace_residueCharacteristic
#print axioms gaussianField2161MinusPlace_residueCharacteristic
#print axioms gaussianField2161PlusPlace_residueCharacteristic_odd
#print axioms gaussianField2161MinusPlace_residueCharacteristic_odd
#print axioms gaussianField2161PlusPlace_comap
#print axioms gaussianField2161MinusPlace_comap
#print axioms gaussianField2161PlusPlace_hasSplitMultiplicativeReductionAt
#print axioms gaussianField2161MinusPlace_hasSplitMultiplicativeReductionAt

end LeanFormal.IUT.XiFPaper.S2701GaussianPrimeIdealsActual
end
