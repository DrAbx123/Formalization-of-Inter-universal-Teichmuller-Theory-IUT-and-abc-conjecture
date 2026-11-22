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
# S2701: the Gaussian prime ideals above 37

The Gaussian integers Z[i] contain the two explicit elements
1 + 6i and 1 - 6i, both of norm 37 = 1^2 + 6^2.  Since 37
is prime, both elements are irreducible, so the principal ideals they
generate are maximal in the Euclidean domain Z[i].

The two maximal ideals are then mapped along the actual ring-of-integers
equivalence GaussianInt = NumberField.RingOfIntegers GaussianField and
give two finite places of the Gaussian field.  Their residue fields are
identified with ZMod 37, hence both residue characteristics are 37
(and odd).

The proof is complete: no proof holes and no extra axioms.
-/

namespace LeanFormal.IUT.XiFPaper.S2786E37PrimeIdealsActual

local instance s2701GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s2701Fact37 : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- The ring of integers of the Gaussian field. -/
abbrev GaussianO : Type := NumberField.RingOfIntegers GaussianField

/-! ## 1. The two Gaussian integers of norm 37 -/

/-- The Gaussian integer 1 + 6i. -/
def gaussianInt37Plus : GaussianInt := ⟨1, 6⟩

/-- The Gaussian integer 1 - 6i. -/
def gaussianInt37Minus : GaussianInt := ⟨1, -6⟩

/-- The norm of 1 + 6i is 37 = 1^2 + 6^2. -/
theorem gaussianInt37Plus_norm :
    Zsqrtd.norm gaussianInt37Plus = 37 := by
  simp [gaussianInt37Plus, Zsqrtd.norm_def]

/-- The norm of 1 - 6i is 37 = 1^2 + 6^2. -/
theorem gaussianInt37Minus_norm :
    Zsqrtd.norm gaussianInt37Minus = 37 := by
  simp [gaussianInt37Minus, Zsqrtd.norm_def]

/-- The actual factorization (1 + 6i)(1 - 6i) = 37. -/
theorem gaussianInt37Plus_mul_minus :
    gaussianInt37Plus * gaussianInt37Minus = (37 : GaussianInt) := by
  apply Zsqrtd.ext_iff.mpr
  constructor <;> norm_num [gaussianInt37Plus, gaussianInt37Minus]

/-- The principal-ideal factorization (37) = (15+44i)(15-44i). -/
theorem gaussianInt37_ideal_factorization :
    Ideal.span {(37 : GaussianInt)} =
      Ideal.span {gaussianInt37Plus} * Ideal.span {gaussianInt37Minus} := by
  rw [← gaussianInt37Plus_mul_minus]
  exact (Ideal.span_singleton_mul_span_singleton _ _).symm

/-- 37 lies in the ideal (1 + 6i). -/
theorem gaussianInt37_mem_plus :
    (37 : GaussianInt) ∈ Ideal.span {gaussianInt37Plus} := by
  rw [← gaussianInt37Plus_mul_minus]
  exact Ideal.mul_mem_right gaussianInt37Minus _
    (Ideal.subset_span (Set.mem_singleton_iff.mpr rfl))

/-- 37 lies in the ideal (1 - 6i). -/
theorem gaussianInt37_mem_minus :
    (37 : GaussianInt) ∈ Ideal.span {gaussianInt37Minus} := by
  rw [Ideal.mem_span_singleton]
  exact ⟨gaussianInt37Plus, by
    rw [mul_comm, gaussianInt37Plus_mul_minus]⟩

/-! ## 2. Irreducibility and maximality in Z[i] -/

/-- 1 + 6i is irreducible: its norm is the prime 37. -/
theorem gaussianInt37Plus_irreducible : Irreducible gaussianInt37Plus := by
  rw [irreducible_iff]
  constructor
  · intro hunit
    have hnorm : (Zsqrtd.norm gaussianInt37Plus).natAbs = 1 :=
      Zsqrtd.norm_eq_one_iff.mpr hunit
    rw [gaussianInt37Plus_norm] at hnorm
    norm_num at hnorm
  · intro a b hab
    have hnorm : (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs = 37 := by
      calc (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs
          = (Zsqrtd.norm (a * b)).natAbs := by rw [Zsqrtd.norm_mul, Int.natAbs_mul]
        _ = (Zsqrtd.norm gaussianInt37Plus).natAbs := by rw [hab]
        _ = 37 := by rw [gaussianInt37Plus_norm]; norm_num
    have hdvd : (Zsqrtd.norm a).natAbs ∣ 37 := ⟨(Zsqrtd.norm b).natAbs, hnorm.symm⟩
    have hcases := s2701Fact37.out.eq_one_or_self_of_dvd
      ((Zsqrtd.norm a).natAbs) hdvd
    rcases hcases with ha | ha
    · left
      exact Zsqrtd.norm_eq_one_iff.mp ha
    · right
      have hb : (Zsqrtd.norm b).natAbs = 1 := by
        rw [ha] at hnorm
        omega
      exact Zsqrtd.norm_eq_one_iff.mp hb

/-- 1 - 6i is irreducible: its norm is the prime 37. -/
theorem gaussianInt37Minus_irreducible : Irreducible gaussianInt37Minus := by
  rw [irreducible_iff]
  constructor
  · intro hunit
    have hnorm : (Zsqrtd.norm gaussianInt37Minus).natAbs = 1 :=
      Zsqrtd.norm_eq_one_iff.mpr hunit
    rw [gaussianInt37Minus_norm] at hnorm
    norm_num at hnorm
  · intro a b hab
    have hnorm : (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs = 37 := by
      calc (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs
          = (Zsqrtd.norm (a * b)).natAbs := by rw [Zsqrtd.norm_mul, Int.natAbs_mul]
        _ = (Zsqrtd.norm gaussianInt37Minus).natAbs := by rw [hab]
        _ = 37 := by rw [gaussianInt37Minus_norm]; norm_num
    have hdvd : (Zsqrtd.norm a).natAbs ∣ 37 := ⟨(Zsqrtd.norm b).natAbs, hnorm.symm⟩
    have hcases := s2701Fact37.out.eq_one_or_self_of_dvd
      ((Zsqrtd.norm a).natAbs) hdvd
    rcases hcases with ha | ha
    · left
      exact Zsqrtd.norm_eq_one_iff.mp ha
    · right
      have hb : (Zsqrtd.norm b).natAbs = 1 := by
        rw [ha] at hnorm
        omega
      exact Zsqrtd.norm_eq_one_iff.mp hb

/-- The principal ideal (1 + 6i) is maximal in Z[i]. -/
theorem gaussianInt37Plus_span_isMaximal :
    (Ideal.span {gaussianInt37Plus}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible gaussianInt37Plus_irreducible

instance gaussianInt37Plus_span_isMaximal_instance :
    (Ideal.span {gaussianInt37Plus}).IsMaximal :=
  gaussianInt37Plus_span_isMaximal

/-- The principal ideal (1 - 6i) is maximal in Z[i]. -/
theorem gaussianInt37Minus_span_isMaximal :
    (Ideal.span {gaussianInt37Minus}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible gaussianInt37Minus_irreducible

instance gaussianInt37Minus_span_isMaximal_instance :
    (Ideal.span {gaussianInt37Minus}).IsMaximal :=
  gaussianInt37Minus_span_isMaximal

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

/-! ## 3. Explicit residue maps Z[i] -> ZMod 37

We have 6^2 = -1 and 1 + 6*6 = 0 modulo 37, and
31^2 = -1 with 1 - 6*31 = 0 modulo 37.  Hence the two
residue maps below kill 1 + 6i and 1 - 6i respectively. -/

/-- The residue map Z[i] -> ZMod 37 sending i to 6. -/
noncomputable def gaussianInt37PlusResidueMap : GaussianInt →+* ZMod 37 :=
  Zsqrtd.lift ⟨(6 : ZMod 37), by decide⟩

/-- The residue map Z[i] -> ZMod 37 sending i to 31 = -6. -/
noncomputable def gaussianInt37MinusResidueMap : GaussianInt →+* ZMod 37 :=
  Zsqrtd.lift ⟨(31 : ZMod 37), by decide⟩

/-- The plus residue map kills 1 + 6i. -/
theorem gaussianInt37PlusResidueMap_generator :
    gaussianInt37PlusResidueMap gaussianInt37Plus = 0 := by
  simp [gaussianInt37PlusResidueMap, gaussianInt37Plus]
  decide

/-- The minus residue map kills 1 - 6i. -/
theorem gaussianInt37MinusResidueMap_generator :
    gaussianInt37MinusResidueMap gaussianInt37Minus = 0 := by
  simp [gaussianInt37MinusResidueMap, gaussianInt37Minus]
  decide

/-- The plus residue map is surjective, already on the integer classes. -/
theorem gaussianInt37PlusResidueMap_surjective :
    Function.Surjective gaussianInt37PlusResidueMap := by
  intro y
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective y
  refine ⟨(a : GaussianInt), ?_⟩
  simp [gaussianInt37PlusResidueMap]

/-- The minus residue map is surjective, already on the integer classes. -/
theorem gaussianInt37MinusResidueMap_surjective :
    Function.Surjective gaussianInt37MinusResidueMap := by
  intro y
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective y
  refine ⟨(a : GaussianInt), ?_⟩
  simp [gaussianInt37MinusResidueMap]

/-- The ideal (1 + 6i) is contained in the kernel of the plus residue map. -/
theorem gaussianInt37Plus_ideal_le_ker :
    Ideal.span {gaussianInt37Plus} ≤
      RingHom.ker gaussianInt37PlusResidueMap := by
  refine Ideal.span_le.mpr ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact (RingHom.mem_ker).mpr gaussianInt37PlusResidueMap_generator

/-- The ideal (1 - 6i) is contained in the kernel of the minus residue map. -/
theorem gaussianInt37Minus_ideal_le_ker :
    Ideal.span {gaussianInt37Minus} ≤
      RingHom.ker gaussianInt37MinusResidueMap := by
  refine Ideal.span_le.mpr ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact (RingHom.mem_ker).mpr gaussianInt37MinusResidueMap_generator

/-- The kernel of the plus residue map is exactly (1 + 6i). -/
theorem gaussianInt37PlusResidueMap_ker :
    RingHom.ker gaussianInt37PlusResidueMap =
      Ideal.span {gaussianInt37Plus} := by
  have hker : (RingHom.ker gaussianInt37PlusResidueMap).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective gaussianInt37PlusResidueMap
      gaussianInt37PlusResidueMap_surjective
  exact (Ideal.IsMaximal.eq_of_le gaussianInt37Plus_span_isMaximal hker.ne_top
    gaussianInt37Plus_ideal_le_ker).symm

/-- The kernel of the minus residue map is exactly (1 - 6i). -/
theorem gaussianInt37MinusResidueMap_ker :
    RingHom.ker gaussianInt37MinusResidueMap =
      Ideal.span {gaussianInt37Minus} := by
  have hker : (RingHom.ker gaussianInt37MinusResidueMap).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective gaussianInt37MinusResidueMap
      gaussianInt37MinusResidueMap_surjective
  exact (Ideal.IsMaximal.eq_of_le gaussianInt37Minus_span_isMaximal hker.ne_top
    gaussianInt37Minus_ideal_le_ker).symm

/-- The two principal ideals are distinct: the plus residue map sends
1 - 6i to 30, which is nonzero modulo 37. -/
theorem gaussianInt37Plus_ne_minus_span :
    Ideal.span {gaussianInt37Plus} ≠ Ideal.span {gaussianInt37Minus} := by
  intro h
  have hmem : gaussianInt37Minus ∈ Ideal.span {gaussianInt37Plus} := by
    rw [h]
    exact Ideal.subset_span (Set.mem_singleton_iff.mpr rfl)
  have hker : gaussianInt37Minus ∈ RingHom.ker gaussianInt37PlusResidueMap :=
    gaussianInt37Plus_ideal_le_ker hmem
  have hzero : gaussianInt37PlusResidueMap gaussianInt37Minus = 0 := hker
  have h2 : gaussianInt37PlusResidueMap gaussianInt37Minus = 2 := by
    simp [gaussianInt37PlusResidueMap, gaussianInt37Minus]
    decide
  rw [h2] at hzero
  exact (by decide : (2 : ZMod 37) ≠ 0) hzero

/-- The residue quotient Z[i]/(15+44i) is ZMod 37. -/
noncomputable def gaussianInt37PlusResidueEquiv :
    (GaussianInt ⧸ Ideal.span {gaussianInt37Plus}) ≃+* ZMod 37 :=
  (Ideal.quotEquivOfEq gaussianInt37PlusResidueMap_ker.symm).trans
    (RingHom.quotientKerEquivOfSurjective gaussianInt37PlusResidueMap_surjective)

/-- The residue quotient Z[i]/(15-44i) is ZMod 37. -/
noncomputable def gaussianInt37MinusResidueEquiv :
    (GaussianInt ⧸ Ideal.span {gaussianInt37Minus}) ≃+* ZMod 37 :=
  (Ideal.quotEquivOfEq gaussianInt37MinusResidueMap_ker.symm).trans
    (RingHom.quotientKerEquivOfSurjective gaussianInt37MinusResidueMap_surjective)

/-- The quotient Z[i]/(15+44i) has 37 elements. -/
theorem gaussianInt37Plus_cardQuot :
    Nat.card (GaussianInt ⧸ Ideal.span {gaussianInt37Plus}) = 37 := by
  calc Nat.card (GaussianInt ⧸ Ideal.span {gaussianInt37Plus})
      = Nat.card (ZMod 37) :=
        Nat.card_congr gaussianInt37PlusResidueEquiv.toEquiv
    _ = 37 := Nat.card_zmod 37

/-- The quotient Z[i]/(15-44i) has 37 elements. -/
theorem gaussianInt37Minus_cardQuot :
    Nat.card (GaussianInt ⧸ Ideal.span {gaussianInt37Minus}) = 37 := by
  calc Nat.card (GaussianInt ⧸ Ideal.span {gaussianInt37Minus})
      = Nat.card (ZMod 37) :=
        Nat.card_congr gaussianInt37MinusResidueEquiv.toEquiv
    _ = 37 := Nat.card_zmod 37

/-- The absolute norm of the principal ideal (15+44i) in Z[i] is 37. -/
theorem gaussianInt37Plus_absNorm :
    Ideal.absNorm (Ideal.span {gaussianInt37Plus}) = 37 := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact gaussianInt37Plus_cardQuot

/-- The absolute norm of the principal ideal (15-44i) in Z[i] is 37. -/
theorem gaussianInt37Minus_absNorm :
    Ideal.absNorm (Ideal.span {gaussianInt37Minus}) = 37 := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact gaussianInt37Minus_cardQuot

/-! ## 4. The corresponding ideals of the ring of integers -/

/-- The prime ideal of the ring of integers of the Gaussian field
corresponding to (1 + 6i). -/
noncomputable def gaussianField37Plus : Ideal GaussianO :=
  Ideal.comap gaussianRingOfIntegersEquivGaussianInt.toRingHom
    (Ideal.span {gaussianInt37Plus})

/-- The prime ideal of the ring of integers corresponding to (1 - 6i). -/
noncomputable def gaussianField37Minus : Ideal GaussianO :=
  Ideal.comap gaussianRingOfIntegersEquivGaussianInt.toRingHom
    (Ideal.span {gaussianInt37Minus})

/-- The image of (15+44i) under the actual ring-of-integers equivalence. -/
theorem gaussianField37Plus_eq_map :
    gaussianField37Plus =
      Ideal.map gaussianIntEquivRingOfIntegers.toRingHom
        (Ideal.span {gaussianInt37Plus}) := by
  rw [gaussianField37Plus]
  exact (Ideal.map_symm (f := gaussianRingOfIntegersEquivGaussianInt)).symm

/-- The image of (15-44i) under the actual ring-of-integers equivalence. -/
theorem gaussianField37Minus_eq_map :
    gaussianField37Minus =
      Ideal.map gaussianIntEquivRingOfIntegers.toRingHom
        (Ideal.span {gaussianInt37Minus}) := by
  rw [gaussianField37Minus]
  exact (Ideal.map_symm (f := gaussianRingOfIntegersEquivGaussianInt)).symm

/-- The transported plus ideal is maximal. -/
instance gaussianField37Plus_isMaximal : gaussianField37Plus.IsMaximal :=
  Ideal.comap_isMaximal_of_equiv gaussianRingOfIntegersEquivGaussianInt

/-- The transported minus ideal is maximal. -/
instance gaussianField37Minus_isMaximal : gaussianField37Minus.IsMaximal :=
  Ideal.comap_isMaximal_of_equiv gaussianRingOfIntegersEquivGaussianInt

/-- The two transported ideals are distinct. -/
theorem gaussianField37Plus_ne_minus :
    gaussianField37Plus ≠ gaussianField37Minus := by
  intro h
  have hmap := congrArg
    (Ideal.map gaussianRingOfIntegersEquivGaussianInt.toRingHom) h
  rw [gaussianField37Plus, gaussianField37Minus,
    Ideal.map_comap_of_surjective
      gaussianRingOfIntegersEquivGaussianInt.toRingHom
      gaussianRingOfIntegersEquivGaussianInt.surjective,
    Ideal.map_comap_of_surjective
      gaussianRingOfIntegersEquivGaussianInt.toRingHom
      gaussianRingOfIntegersEquivGaussianInt.surjective] at hmap
  exact gaussianInt37Plus_ne_minus_span hmap

/-- The residue quotient of the transported plus ideal is ZMod 37. -/
noncomputable def gaussianField37PlusResidueEquiv :
    (GaussianO ⧸ gaussianField37Plus) ≃+* ZMod 37 :=
  (Ideal.quotientEquiv (gaussianField37Plus)
    (Ideal.span {gaussianInt37Plus})
    gaussianRingOfIntegersEquivGaussianInt
    (by
      change Ideal.span {gaussianInt37Plus} =
        Ideal.map gaussianRingOfIntegersEquivGaussianInt.toRingHom
          gaussianField37Plus
      rw [gaussianField37Plus,
        Ideal.map_comap_of_surjective
          gaussianRingOfIntegersEquivGaussianInt.toRingHom
          gaussianRingOfIntegersEquivGaussianInt.surjective])).trans
    gaussianInt37PlusResidueEquiv

/-- The residue quotient of the transported minus ideal is ZMod 37. -/
noncomputable def gaussianField37MinusResidueEquiv :
    (GaussianO ⧸ gaussianField37Minus) ≃+* ZMod 37 :=
  (Ideal.quotientEquiv (gaussianField37Minus)
    (Ideal.span {gaussianInt37Minus})
    gaussianRingOfIntegersEquivGaussianInt
    (by
      change Ideal.span {gaussianInt37Minus} =
        Ideal.map gaussianRingOfIntegersEquivGaussianInt.toRingHom
          gaussianField37Minus
      rw [gaussianField37Minus,
        Ideal.map_comap_of_surjective
          gaussianRingOfIntegersEquivGaussianInt.toRingHom
          gaussianRingOfIntegersEquivGaussianInt.surjective])).trans
    gaussianInt37MinusResidueEquiv

/-- The absolute norm of the transported plus ideal is 37. -/
theorem gaussianField37Plus_absNorm :
    Ideal.absNorm gaussianField37Plus = 37 := by
  rw [Ideal.absNorm_apply]
  rw [Submodule.cardQuot_apply]
  calc Nat.card (GaussianO ⧸ gaussianField37Plus)
      = Nat.card (ZMod 37) :=
        Nat.card_congr gaussianField37PlusResidueEquiv.toEquiv
    _ = 37 := Nat.card_zmod 37

/-- The absolute norm of the transported minus ideal is 37. -/
theorem gaussianField37Minus_absNorm :
    Ideal.absNorm gaussianField37Minus = 37 := by
  rw [Ideal.absNorm_apply]
  rw [Submodule.cardQuot_apply]
  calc Nat.card (GaussianO ⧸ gaussianField37Minus)
      = Nat.card (ZMod 37) :=
        Nat.card_congr gaussianField37MinusResidueEquiv.toEquiv
    _ = 37 := Nat.card_zmod 37

/-! ## 5. The two finite places and their residue characteristics -/

/-- The finite place of the Gaussian field at (1 + 6i). -/
noncomputable def gaussianField37PlusPlace : NumberField.FinitePlace GaussianField :=
  NumberField.FinitePlace.mk
    { asIdeal := gaussianField37Plus
      isPrime := gaussianField37Plus_isMaximal.isPrime
      ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField
        gaussianField37Plus_isMaximal
        (NumberField.RingOfIntegers.not_isField GaussianField) }

/-- The finite place of the Gaussian field at (1 - 6i). -/
noncomputable def gaussianField37MinusPlace : NumberField.FinitePlace GaussianField :=
  NumberField.FinitePlace.mk
    { asIdeal := gaussianField37Minus
      isPrime := gaussianField37Minus_isMaximal.isPrime
      ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField
        gaussianField37Minus_isMaximal
        (NumberField.RingOfIntegers.not_isField GaussianField) }

/-- The maximal ideal of the plus place is the transported plus ideal. -/
theorem gaussianField37PlusPlace_maximalIdeal :
    gaussianField37PlusPlace.maximalIdeal.asIdeal = gaussianField37Plus :=
  congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
    (NumberField.FinitePlace.maximalIdeal_mk _)

/-- The maximal ideal of the minus place is the transported minus ideal. -/
theorem gaussianField37MinusPlace_maximalIdeal :
    gaussianField37MinusPlace.maximalIdeal.asIdeal = gaussianField37Minus :=
  congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
    (NumberField.FinitePlace.maximalIdeal_mk _)

/-- The two finite places are distinct. -/
theorem gaussianField37PlusPlace_ne_minusPlace :
    gaussianField37PlusPlace ≠ gaussianField37MinusPlace := by
  intro h
  have hmax := congrArg NumberField.FinitePlace.maximalIdeal h
  have hasIdeal := congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hmax
  rw [gaussianField37PlusPlace_maximalIdeal,
    gaussianField37MinusPlace_maximalIdeal] at hasIdeal
  exact gaussianField37Plus_ne_minus hasIdeal

/-- The residue characteristic of the plus place is 37. -/
theorem gaussianField37PlusPlace_residueCharacteristic :
    NumberFieldFinitePlace.residueCharacteristic gaussianField37PlusPlace = 37 := by
  rw [NumberFieldFinitePlace.residueCharacteristic]
  change ringChar (GaussianO ⧸ gaussianField37PlusPlace.maximalIdeal.asIdeal) = 37
  rw [gaussianField37PlusPlace_maximalIdeal]
  rw [ringChar.eq_iff]
  exact (RingHom.charP_iff
    (gaussianField37PlusResidueEquiv :
      (GaussianO ⧸ gaussianField37Plus) →+* ZMod 37)
    gaussianField37PlusResidueEquiv.injective 37).mpr inferInstance

/-- The residue characteristic of the minus place is 37. -/
theorem gaussianField37MinusPlace_residueCharacteristic :
    NumberFieldFinitePlace.residueCharacteristic gaussianField37MinusPlace = 37 := by
  rw [NumberFieldFinitePlace.residueCharacteristic]
  change ringChar (GaussianO ⧸ gaussianField37MinusPlace.maximalIdeal.asIdeal) = 37
  rw [gaussianField37MinusPlace_maximalIdeal]
  rw [ringChar.eq_iff]
  exact (RingHom.charP_iff
    (gaussianField37MinusResidueEquiv :
      (GaussianO ⧸ gaussianField37Minus) →+* ZMod 37)
    gaussianField37MinusResidueEquiv.injective 37).mpr inferInstance

/-- The residue characteristic of the plus place is odd. -/
theorem gaussianField37PlusPlace_residueCharacteristic_odd :
    Odd (NumberFieldFinitePlace.residueCharacteristic gaussianField37PlusPlace) := by
  rw [gaussianField37PlusPlace_residueCharacteristic]
  exact ⟨18, by norm_num⟩

/-- The residue characteristic of the minus place is odd. -/
theorem gaussianField37MinusPlace_residueCharacteristic_odd :
    Odd (NumberFieldFinitePlace.residueCharacteristic gaussianField37MinusPlace) := by
  rw [gaussianField37MinusPlace_residueCharacteristic]
  exact ⟨18, by norm_num⟩



#check gaussianField37PlusPlace
#check gaussianField37MinusPlace
#check gaussianField37PlusPlace_residueCharacteristic
#check gaussianField37MinusPlace_residueCharacteristic
#print axioms gaussianField37PlusPlace_residueCharacteristic

end LeanFormal.IUT.XiFPaper.S2786E37PrimeIdealsActual
end
