import tmp.sheaf.xif.paper.S1715SourceTorsionClauseActual
import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Tactic

/-!
# S1717: the S1667 curve at the bad place 7, and the actual D5 clause at l = 5

S1715 constructs the paper's Definition 3.1(c) clause (D5) for the actual
S1667 curve over the actual number field S1687Field, but only at the actual
place above the rational prime 5.  The residue characteristic there is 5, so
the clause's lTorsionCompatible condition (l prime to the residue
characteristic) is *false* at l = 5; S1715 proves that the faithful clause
cannot exist at l = 5 with that place.

The paper's bad-place input, however, allows any bad place p with
comap p in V_bad^mod.  The S1667 curve also has split multiplicative
reduction at the rational prime 7, so place 7 is an admissible alternative
bad place.  This file removes the l = 5 obstruction by using that place:

* concreteSevenPlace is the actual rational finite place at 7, built from
  Mathlib's height-one-prime/primes equivalence exactly as the existing
  five-place construction.
* The integral model I0 over Z_7, with a_2 = 61/64 and a_4 = -125/64 (both
  7-adic units), has c_4 = 27721/256 a 7-adic unit and v_7(Delta) = 2.  Its
  reduction is y^2 = x^3 + 5x^2 + x over F_7, with c_4 = 2 and Delta = 0;
  the tangent polynomial is 2T^2 + 5, whose discriminant is 2 = 3^2, so it
  splits.  Hence split multiplicative reduction at 7 is proved for the
  actual completion and for the global punctured curve at
  concreteSevenPlace.
* S1687PlaceAboveSeven is an actual finite place of S1687Field above
  concreteSevenPlace, obtained from comap_surjective; split multiplicative
  reduction transports to it by base change.
* A generic D5 clause S1717SourceTorsionClause is parameterized by
  place/split/odd/residue-characteristic data.  At l = 5 it is
  instantiated with place 7, residue characteristic 7 and compatibility
  Nat.Coprime 5 7, producing the actual l = 5 clause, still conditional
  on the explicit source input S1715ImageContainsSL2 (the literal
  SL_2(F_l) containment; no basis or large-image statement is assumed).
* Admissibility (S1667Admissible) continues to use the place above 5; it
  needs no new place.  Only the D5 clause is moved to place 7.  The two
  places are proved distinct.

No sorry, no axiom, no True-image placeholder and no arbitrary basis is
used.  The only conditional input is the explicit image statement, exactly
as in S1715.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1717PlaceSevenD5Actual

open Polynomial WeierstrassCurve
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1712OddResidueActual
open LeanFormal.IUT.XiFPaper.S1714AdmissibleActual
open LeanFormal.IUT.XiFPaper.S1715SourceTorsionClauseActual
open LeanFormal.IUT.Theorem311Source

local instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

/-! ## 1. The actual rational finite place at 7 -/

/-- The rational local field at 7. -/
abbrev K7 := ℚ_[7]

/-- The 7-adic integers. -/
abbrev R7 := ℤ_[7]

def concreteSevenPrime : Nat.Primes :=
  ⟨7, Nat.prime_seven⟩

def concreteSevenHeightOne :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm
    concreteSevenPrime

/-- The actual rational finite place at the prime 7. -/
def concreteSevenPlace : NumberField.FinitePlace ℚ :=
  NumberField.FinitePlace.mk concreteSevenHeightOne

@[simp] theorem concreteSevenPlace_maximalIdeal :
    concreteSevenPlace.maximalIdeal = concreteSevenHeightOne := by
  exact NumberField.FinitePlace.maximalIdeal_mk concreteSevenHeightOne

@[simp] theorem concreteSevenPlace_underlyingPrime :
    NumberFieldFinitePlace.underlyingPrime concreteSevenPlace =
      concreteSevenHeightOne := by
  exact concreteSevenPlace_maximalIdeal

theorem concreteSevenHeightOne_natGenerator :
    Rat.HeightOneSpectrum.natGenerator concreteSevenHeightOne = 7 := by
  exact congrArg (fun p : Nat.Primes => p.1)
    ((Rat.HeightOneSpectrum.primesEquiv
      (R := NumberField.RingOfIntegers ℚ)).apply_symm_apply concreteSevenPrime)

theorem concreteSevenHeightOne_seven_mem :
    (7 : NumberField.RingOfIntegers ℚ) ∈ concreteSevenHeightOne.asIdeal := by
  apply (Ideal.apply_mem_of_equiv_iff
    (I := concreteSevenHeightOne.asIdeal)
    (f := Rat.IsIntegralClosure.intEquiv
      (NumberField.RingOfIntegers ℚ))).mp
  have hdiv : Rat.HeightOneSpectrum.natGenerator concreteSevenHeightOne ∣ 7 := by
    rw [concreteSevenHeightOne_natGenerator]
  have hmap :=
    (Rat.HeightOneSpectrum.natGenerator_dvd_iff concreteSevenHeightOne).mp hdiv
  convert hmap using 1
  rw [Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv]
  exact map_intCast Rat.ringOfIntegersEquiv 7

/-- The height-one prime is the principal ideal generated by 7 in the
rational ring of integers. -/
theorem concreteSevenHeightOne_asIdeal_eq_span :
    concreteSevenHeightOne.asIdeal =
      Ideal.span {(7 : NumberField.RingOfIntegers ℚ)} := by
  let e : NumberField.RingOfIntegers ℚ ≃+* ℤ :=
    Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)
  have h := Rat.HeightOneSpectrum.span_natGenerator
    (R := NumberField.RingOfIntegers ℚ) concreteSevenHeightOne
  rw [concreteSevenHeightOne_natGenerator] at h
  change Ideal.span {(7 : ℤ)} =
    Ideal.map e.toRingHom concreteSevenHeightOne.asIdeal at h
  have h' := congrArg (Ideal.map e.symm.toRingHom) h
  rw [Ideal.map_span] at h'
  simp only [Set.image_singleton] at h'
  simp at h'
  exact h'.symm

/-- The residue characteristic of the rational place 7 is 7. -/
theorem concreteSevenPlace_residueCharacteristic :
    NumberFieldFinitePlace.residueCharacteristic concreteSevenPlace = 7 := by
  rw [NumberFieldFinitePlace.residueCharacteristic]
  change ringChar (NumberField.RingOfIntegers ℚ ⧸
    concreteSevenPlace.maximalIdeal.asIdeal) = 7
  rw [concreteSevenPlace_maximalIdeal, concreteSevenHeightOne_asIdeal_eq_span]
  rw [Ideal.ringChar_quot]
  have hunder : Ideal.under ℤ
      (Ideal.span {(7 : NumberField.RingOfIntegers ℚ)}) =
      Ideal.span {(7 : ℤ)} := by
    ext x
    rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, hy⟩
      let e : NumberField.RingOfIntegers ℚ ≃+* ℤ :=
        Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)
      have he : e (algebraMap ℤ (NumberField.RingOfIntegers ℚ) x) = x := by
        simp
      have hy' := congrArg e hy
      rw [map_mul, map_ofNat, he] at hy'
      exact ⟨e y, hy'⟩
    · rintro ⟨y, rfl⟩
      exact ⟨algebraMap ℤ (NumberField.RingOfIntegers ℚ) y, by
        rw [map_mul, map_ofNat]⟩
  rw [hunder, Ideal.absNorm_span_singleton]
  norm_num

abbrev concreteSevenCompletion := concreteSevenHeightOne.adicCompletion ℚ

/-- Pin the algebra structure on the completed field to the canonical
adic-completion structure; this avoids the generic division-ring instance
diamond with the field structure. -/
local instance : Algebra ℚ concreteSevenCompletion :=
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
    (NumberField.RingOfIntegers ℚ) ℚ concreteSevenHeightOne

abbrev concreteSevenCompletionIntegers :=
  concreteSevenHeightOne.adicCompletionIntegers ℚ

noncomputable def concreteSevenPadicEquiv :
    K7 ≃A[ℚ] concreteSevenCompletion :=
  Padic.adicCompletionEquiv (R := NumberField.RingOfIntegers ℚ) concreteSevenPrime

noncomputable def concreteSevenPadicIntEquiv :
    R7 ≃A[ℤ] concreteSevenCompletionIntegers :=
  PadicInt.adicCompletionIntegersEquiv (R := NumberField.RingOfIntegers ℚ)
    concreteSevenPrime

theorem concreteSevenPadicEquiv_algebraMap (x : ℚ) :
    concreteSevenPadicEquiv (algebraMap ℚ K7 x) =
      algebraMap ℚ concreteSevenCompletion x := by
  exact concreteSevenPadicEquiv.commutes x

theorem concreteSevenPadicIntEquiv_coe (x : R7) :
    (concreteSevenPadicIntEquiv x : concreteSevenCompletion) =
      concreteSevenPadicEquiv (x : K7) := by
  exact PadicInt.coe_adicCompletionIntegersEquiv_apply
    (R := NumberField.RingOfIntegers ℚ) concreteSevenPrime x

/-! ## 2. Split multiplicative reduction of the S1667 curve at 7 -/

/-- 61/64 is a 7-adic unit. -/
lemma norm_61_64 : ‖(61 / 64 : K7)‖ = 1 := by
  rw [show (61 / 64 : K7) = ((61 : ℕ) : K7) / ((64 : ℕ) : K7) by norm_num]
  rw [norm_div]
  have h1 : ‖((61 : ℕ) : K7)‖ = 1 :=
    (Padic.norm_natCast_eq_one_iff (p := 7) (n := 61)).2 (by norm_num)
  have h2 : ‖((64 : ℕ) : K7)‖ = 1 :=
    (Padic.norm_natCast_eq_one_iff (p := 7) (n := 64)).2 (by norm_num)
  rw [h1, h2]
  norm_num

/-- -125/64 is a 7-adic unit (this is the structural difference from the
place 5, where -125/64 is a uniformizer). -/
lemma norm_neg125_64_eq_one : ‖(-125 / 64 : K7)‖ = 1 := by
  rw [show (-125 / 64 : K7) =
    ((-125 : ℤ) : K7) / ((64 : ℕ) : K7) by norm_num]
  rw [norm_div]
  have h1 : ‖((-125 : ℤ) : K7)‖ = 1 := by
    rw [Padic.norm_intCast_eq_one_iff]
    norm_num
  have h2 : ‖((64 : ℕ) : K7)‖ = 1 :=
    (Padic.norm_natCast_eq_one_iff (p := 7) (n := 64)).2 (by norm_num)
  rw [h1, h2, div_one]

/-- The lift of 61/64 to Z_7. -/
def z2 : R7 := ⟨(61 / 64 : K7), le_of_eq norm_61_64⟩

/-- The lift of -125/64 to Z_7. -/
def z4 : R7 := ⟨(-125 / 64 : K7), le_of_eq norm_neg125_64_eq_one⟩

/-- The explicit integral model of the S1667 curve at 7. -/
def I0 : WeierstrassCurve R7 :=
  WeierstrassCurve.mk 0 z2 0 z4 0

lemma z2_mul_64 : z2 * (64 : R7) = (61 : R7) := by
  apply Subtype.ext
  change (61 / 64 : K7) * (64 : K7) = (61 : K7)
  norm_num

lemma z4_mul_64 : z4 * (64 : R7) = (-125 : R7) := by
  apply Subtype.ext
  change (-125 / 64 : K7) * (64 : K7) = (-125 : K7)
  norm_num

/-- The integral model base-changes to the completion of the S1667 curve. -/
theorem I0_baseChange :
    I0.map (algebraMap R7 K7) = S1667Curve.baseChange K7 := by
  ext <;> simp [I0, z2, z4, S1667Curve, WeierstrassCurve.baseChange]

/-- The discriminant numerator is divisible by 7^2 but not 7^3, and the
denominator is prime to 7: v_7(Delta) = 2 for the S1667 discriminant. -/
theorem S1717Curve_delta_seven_valuation_eq_two :
    S1667Curve.Δ = (558140625 / 1048576 : ℚ) ∧
      (7 ^ 2 : ℕ) ∣ 558140625 ∧
      ¬ ((7 ^ 3 : ℕ) ∣ 558140625) ∧
      ¬ ((7 : ℕ) ∣ 1048576) := by
  refine ⟨S1667Curve_Δ, by norm_num, by norm_num, by norm_num⟩

/-- The c_4 numerator 27721 and denominator 256 are both prime to 7, so
c_4 = 27721/256 is a 7-adic unit (v_7(c_4) = 0). -/
theorem S1717Curve_c4_seven_valuation_eq_zero :
    S1667Curve.c₄ = (27721 / 256 : ℚ) ∧
      ¬ ((7 : ℕ) ∣ 27721) ∧
      ¬ ((7 : ℕ) ∣ 256) := by
  refine ⟨S1667Curve_c₄, by norm_num, by norm_num⟩

/-- The reduction of the integral model, over F_7. -/
def J : WeierstrassCurve (ZMod 7) :=
  I0.map (PadicInt.toZMod (p := 7))

lemma toZMod_64 : PadicInt.toZMod (p := 7) (64 : R7) = 1 := by
  rw [show (64 : R7) = ((64 : ℕ) : R7) by norm_num]
  rw [map_natCast]
  decide

lemma toZMod_61 : PadicInt.toZMod (p := 7) (61 : R7) = 5 := by
  rw [show (61 : R7) = ((61 : ℕ) : R7) by norm_num]
  rw [map_natCast]
  decide

lemma toZMod_neg125 : PadicInt.toZMod (p := 7) (-125 : R7) = 1 := by
  rw [show (-125 : R7) = ((-125 : ℤ) : R7) by norm_num]
  rw [map_intCast]
  decide

lemma toZMod_z2 : PadicInt.toZMod (p := 7) z2 = 5 := by
  have hz : PadicInt.toZMod (p := 7) z2 * (1 : ZMod 7) = 5 := by
    have h := congrArg (PadicInt.toZMod (p := 7)) z2_mul_64
    rw [map_mul, toZMod_64, toZMod_61] at h
    exact h
  simpa using hz

lemma toZMod_z4 : PadicInt.toZMod (p := 7) z4 = 1 := by
  have hz : PadicInt.toZMod (p := 7) z4 * (1 : ZMod 7) = 1 := by
    have h := congrArg (PadicInt.toZMod (p := 7)) z4_mul_64
    rw [map_mul, toZMod_64, toZMod_neg125] at h
    exact h
  simpa using hz

lemma J_eq : J = WeierstrassCurve.mk (0 : ZMod 7) 5 0 1 0 := by
  ext <;> simp [J, I0, toZMod_z2, toZMod_z4]

lemma J_c4 : J.c₄ = (2 : ZMod 7) := by
  rw [J_eq]
  decide

lemma J_delta : J.Δ = (0 : ZMod 7) := by
  rw [J_eq]
  decide

lemma J_a1 : J.a₁ = (0 : ZMod 7) := by
  rw [J_eq]

lemma J_splitConstant :
    54 * J.b₆ - 3 * J.b₂ * J.b₄ + J.a₂ * J.c₄ = (2 : ZMod 7) := by
  rw [J_eq]
  decide

/-- The tangent polynomial of the reduced model is 2T^2 + 5. -/
lemma J_splitReductionPolynomial :
    splitReductionPolynomial J = (2 * X ^ 2 + 5 : (ZMod 7)[X]) := by
  have hmain : splitReductionPolynomial J = C 2 * X ^ 2 - C 2 := by
    rw [splitReductionPolynomial, J_splitConstant, J_c4, J_a1]
    simp only [mul_zero, C_0, zero_mul, add_zero]
  rw [hmain, sub_eq_add_neg, ← C_neg]
  rw [show (-(2 : ZMod 7)) = 5 from by decide]
  simp only [Polynomial.C_ofNat]

/-- 2T^2 + 5 = 2 (T - 1)(T + 1) over F_7. -/
lemma two_X_sq_add_five_factor :
    (2 * X ^ 2 + 5 : (ZMod 7)[X]) = C 2 * (X - C 1) * (X + C 1) := by
  rw [show (2 * X ^ 2 + 5 : (ZMod 7)[X]) = C 2 * X ^ 2 - C 2 by
    rw [sub_eq_add_neg, ← C_neg]
    rw [show (-(2 : ZMod 7)) = 5 from by decide]
    simp only [Polynomial.C_ofNat]]
  simp only [Polynomial.C_1]
  ring

/-- The tangent polynomial splits over the residue field F_7. -/
lemma two_X_sq_add_five_splits :
    (2 * X ^ 2 + 5 : (ZMod 7)[X]).Splits := by
  rw [two_X_sq_add_five_factor]
  exact ((Polynomial.Splits.C 2).mul (Polynomial.Splits.X_sub_C 1)).mul
    (Polynomial.Splits.X_add_C 1)

/-- The discriminant of 2T^2 + 5 over F_7 is 2 = 3^2. -/
lemma two_X_sq_add_five_discriminant :
    ((0 : ZMod 7) ^ 2 - 4 * 2 * 5 = (3 : ZMod 7) ^ 2) := by
  decide

/-- The two roots 1 and -1 of 2T^2 + 5 over F_7. -/
lemma two_X_sq_add_five_roots :
    (2 * (1 : ZMod 7) ^ 2 + 5 = 0) ∧
      (2 * (6 : ZMod 7) ^ 2 + 5 = 0) := by
  constructor <;> decide

lemma toZMod_I0_c4 : PadicInt.toZMod (p := 7) I0.c₄ = 2 := by
  rw [← WeierstrassCurve.map_c₄ (f := PadicInt.toZMod (p := 7)) (W := I0)]
  exact J_c4

lemma toZMod_I0_delta : PadicInt.toZMod (p := 7) I0.Δ = 0 := by
  rw [← WeierstrassCurve.map_Δ (f := PadicInt.toZMod (p := 7)) (W := I0)]
  exact J_delta

lemma I0_c4_notMem_maximalIdeal : I0.c₄ ∉ IsLocalRing.maximalIdeal R7 := by
  rw [← PadicInt.ker_toZMod (p := 7)]
  intro h
  have hzero : PadicInt.toZMod (p := 7) I0.c₄ = 0 := RingHom.mem_ker.mp h
  rw [toZMod_I0_c4] at hzero
  exact (by decide : (2 : ZMod 7) ≠ 0) hzero

lemma I0_delta_mem_maximalIdeal : I0.Δ ∈ IsLocalRing.maximalIdeal R7 := by
  rw [← PadicInt.ker_toZMod (p := 7)]
  exact RingHom.mem_ker.mpr toZMod_I0_delta

theorem W7_isIntegral :
    WeierstrassCurve.IsIntegral R7 (S1667Curve.baseChange K7) :=
  ⟨⟨I0, I0_baseChange.symm⟩⟩

attribute [local instance] W7_isIntegral

theorem I0_integralModel_eq :
    (S1667Curve.baseChange K7).integralModel R7 = I0 := by
  letI : WeierstrassCurve.IsIntegral R7 (S1667Curve.baseChange K7) := W7_isIntegral
  apply WeierstrassCurve.map_injective
    (FaithfulSMul.algebraMap_injective R7 K7)
  change ((S1667Curve.baseChange K7).integralModel R7).baseChange K7 =
    I0.baseChange K7
  rw [WeierstrassCurve.baseChange_integralModel_eq]
  exact I0_baseChange.symm

theorem W7_c4_valuation :
    (IsDiscreteValuationRing.maximalIdeal R7).valuation K7
      (S1667Curve.baseChange K7).c₄ = 1 := by
  letI : WeierstrassCurve.IsIntegral R7 (S1667Curve.baseChange K7) := W7_isIntegral
  rw [← WeierstrassCurve.integralModel_c₄_eq R7 (S1667Curve.baseChange K7)]
  rw [I0_integralModel_eq]
  exact ((IsDiscreteValuationRing.maximalIdeal R7).valuation_eq_one_iff_notMem
    (K := K7)).mpr I0_c4_notMem_maximalIdeal

theorem W7_delta_valuation_lt_one :
    (IsDiscreteValuationRing.maximalIdeal R7).valuation K7
      (S1667Curve.baseChange K7).Δ < 1 := by
  letI : WeierstrassCurve.IsIntegral R7 (S1667Curve.baseChange K7) := W7_isIntegral
  rw [← WeierstrassCurve.integralModel_Δ_eq R7 (S1667Curve.baseChange K7)]
  rw [I0_integralModel_eq]
  exact ((IsDiscreteValuationRing.maximalIdeal R7).valuation_lt_one_iff_mem
    (K := K7) I0.Δ).mpr I0_delta_mem_maximalIdeal

theorem W7_isMinimal :
    WeierstrassCurve.IsMinimal R7 (S1667Curve.baseChange K7) := by
  letI : WeierstrassCurve.IsIntegral R7 (S1667Curve.baseChange K7) := W7_isIntegral
  exact isMinimal_of_isIntegral_valuation_c₄_eq_one R7
    (S1667Curve.baseChange K7) W7_c4_valuation

theorem W7_hasMultiplicativeReduction :
    (S1667Curve.baseChange K7).HasMultiplicativeReduction R7 := by
  letI : WeierstrassCurve.IsIntegral R7 (S1667Curve.baseChange K7) := W7_isIntegral
  letI : WeierstrassCurve.IsMinimal R7 (S1667Curve.baseChange K7) := W7_isMinimal
  exact
    { badReduction := W7_delta_valuation_lt_one
      multiplicativeReduction := W7_c4_valuation }

theorem W7_hasSplitMultiplicativeReduction :
    (S1667Curve.baseChange K7).HasSplitMultiplicativeReduction R7 := by
  letI : WeierstrassCurve.IsIntegral R7 (S1667Curve.baseChange K7) := W7_isIntegral
  letI : WeierstrassCurve.IsMinimal R7 (S1667Curve.baseChange K7) := W7_isMinimal
  letI : (S1667Curve.baseChange K7).HasMultiplicativeReduction R7 :=
    W7_hasMultiplicativeReduction
  refine { splitMultiplicativeReduction := ?_ }
  rw [I0_integralModel_eq]
  change Polynomial.Splits
    ((splitReductionPolynomial I0).map
      (algebraMap R7 (IsLocalRing.ResidueField R7)))
  let P : (IsLocalRing.ResidueField R7)[X] :=
    (splitReductionPolynomial I0).map (IsLocalRing.residue R7)
  let rf : IsLocalRing.ResidueField R7 ≃+* ZMod 7 :=
    PadicInt.residueField (p := 7)
  have hcomp : rf.toRingHom.comp (IsLocalRing.residue R7) =
      PadicInt.toZMod (p := 7) :=
    (PadicInt.toZMod_eq_residueField_comp_residue (p := 7)).symm
  have hP : P.map rf.toRingHom = (2 * X ^ 2 + 5 : (ZMod 7)[X]) := by
    calc P.map rf.toRingHom
        = (splitReductionPolynomial I0).map
            (rf.toRingHom.comp (IsLocalRing.residue R7)) := by
          simp only [P, Polynomial.map_map]
      _ = (splitReductionPolynomial I0).map (PadicInt.toZMod (p := 7)) := by
          rw [hcomp]
      _ = splitReductionPolynomial J := by
          rw [J, splitReductionPolynomial_map]
      _ = (2 * X ^ 2 + 5 : (ZMod 7)[X]) := J_splitReductionPolynomial
  have hsplit : (P.map rf.toRingHom).Splits := by
    rw [hP]
    exact two_X_sq_add_five_splits
  exact Polynomial.Splits.of_splits_map rf.toRingHom hsplit
    (fun a _ => ⟨rf.symm a, by simp⟩)

/-! ## 3. The split reduction as a statement at the rational place 7 -/

/-- The punctured S1667 curve has split multiplicative reduction at the
actual rational place 7. -/
theorem S1717_splitMultiplicativeReductionAtSeven :
    S1667Punctured.HasSplitMultiplicativeReductionAt concreteSevenPlace := by
  have hW : HasSplitMultiplicativeReductionOnMinimalModel R7
      (S1667Curve.baseChange K7) :=
    ⟨1, by simpa using W7_hasSplitMultiplicativeReduction⟩
  have hcomm :
      concreteSevenPadicEquiv.toRingEquiv.toRingHom.comp (algebraMap R7 K7) =
      (algebraMap concreteSevenCompletionIntegers concreteSevenCompletion).comp
        concreteSevenPadicIntEquiv.toRingEquiv.toRingHom := by
    apply RingHom.ext
    intro x
    dsimp only [RingHom.comp_apply]
    change concreteSevenPadicEquiv
        (algebraMap R7 K7 x) =
      algebraMap concreteSevenCompletionIntegers concreteSevenCompletion
        (concreteSevenPadicIntEquiv x)
    change concreteSevenPadicEquiv
        (algebraMap R7 K7 x) =
      (concreteSevenPadicIntEquiv x : concreteSevenCompletion)
    rw [concreteSevenPadicIntEquiv_coe]
    congr 1
  letI : IsLocalHom concreteSevenPadicIntEquiv.toRingEquiv.toRingHom := by
    refine ⟨fun x hx => ?_⟩
    simpa using hx.map concreteSevenPadicIntEquiv.toRingEquiv.symm.toMonoidHom
  have hmap := hasSplitMultiplicativeReductionOnMinimalModel_map_of_commutes
    (R := R7) (S := concreteSevenCompletionIntegers)
    (K := K7) (L := concreteSevenCompletion)
    concreteSevenPadicIntEquiv.toRingEquiv.toRingHom
    concreteSevenPadicEquiv.toRingEquiv.toRingHom
    hcomm (S1667Curve.baseChange K7) hW
  have hWmap :
      (S1667Curve.baseChange K7).map
        concreteSevenPadicEquiv.toRingEquiv.toRingHom =
      S1667Curve.baseChange concreteSevenCompletion := by
    have hcomp :
        concreteSevenPadicEquiv.toRingEquiv.toRingHom.comp
          (algebraMap ℚ K7) =
        algebraMap ℚ concreteSevenCompletion := by
      apply RingHom.ext
      intro q
      exact concreteSevenPadicEquiv_algebraMap q
    change S1667Curve.map
        (concreteSevenPadicEquiv.toRingEquiv.toRingHom.comp
          (algebraMap ℚ K7)) =
      S1667Curve.map (algebraMap ℚ concreteSevenCompletion)
    rw [hcomp]
  rw [hWmap] at hmap
  unfold PuncturedEllipticCurve.HasSplitMultiplicativeReductionAt
  let F : ∀ z : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ℚ), WeierstrassCurve (z.adicCompletion ℚ) :=
    fun z =>
      letI : Algebra ℚ (z.adicCompletion ℚ) :=
        IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
          (NumberField.RingOfIntegers ℚ) ℚ z
      S1667Curve.baseChange (z.adicCompletion ℚ)
  have htransport :=
    transport_splitMultiplicativeReduction_along_heightOne_eq F
      concreteSevenPlace_underlyingPrime.symm
      (by
        change HasSplitMultiplicativeReductionOnMinimalModel
          concreteSevenCompletionIntegers
          (S1667Curve.baseChange concreteSevenCompletion)
        exact hmap)
  simpa [F, S1667Punctured] using htransport

/-! ## 4. The actual place of S1687Field above 7 -/

/-- An actual finite place of the S1687 field above the rational place 7,
obtained from the actual lying-over surjectivity. -/
noncomputable def S1687PlaceAboveSeven : NumberField.FinitePlace S1687Field :=
  Classical.choose
    (NumberFieldFinitePlace.comap_surjective
      (k := ℚ) (K := S1687Field) concreteSevenPlace)

theorem S1687PlaceAboveSeven_comap :
    NumberFieldFinitePlace.comap (k := ℚ) S1687PlaceAboveSeven =
      concreteSevenPlace :=
  Classical.choose_spec
    (NumberFieldFinitePlace.comap_surjective
      (k := ℚ) (K := S1687Field) concreteSevenPlace)

/-- Split multiplicative reduction at the rational place 7 transports to the
actual place above 7. -/
theorem S1717Split_of_rational
    (h : S1667Punctured.HasSplitMultiplicativeReductionAt concreteSevenPlace) :
    (S1667Punctured.baseChange S1687Field).HasSplitMultiplicativeReductionAt
      S1687PlaceAboveSeven := by
  apply PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_baseChange
  rw [S1687PlaceAboveSeven_comap]
  exact h

/-- The actual curve S1715Curve has split multiplicative reduction at the
actual place above 7. -/
theorem S1717SplitAtPlaceSeven :
    S1715Curve.HasSplitMultiplicativeReductionAt S1687PlaceAboveSeven :=
  S1717Split_of_rational S1717_splitMultiplicativeReductionAtSeven

/-- The residue characteristic of the actual place above 7 is 7. -/
theorem S1717ResidueCharacteristic_placeAboveSeven :
    NumberFieldFinitePlace.residueCharacteristic S1687PlaceAboveSeven = 7 := by
  have h := NumberFieldFinitePlace.residueCharacteristic_comap
    (k := ℚ) (K := S1687Field) S1687PlaceAboveSeven
  rw [S1687PlaceAboveSeven_comap] at h
  rw [← h, concreteSevenPlace_residueCharacteristic]

/-- The actual place above 7 has odd residue characteristic. -/
theorem S1717OddResidue_placeAboveSeven :
    Odd (NumberFieldFinitePlace.residueCharacteristic S1687PlaceAboveSeven) := by
  rw [S1717ResidueCharacteristic_placeAboveSeven]
  exact ⟨3, by norm_num⟩

/-! ## 5. The generic D5 clause, and its instantiation at l = 5 -/

/-- The concrete prime label l = 5. -/
def S1717Five : PrimeGeFive := S1715Five

@[simp] theorem S1717Five_value : S1717Five.value = 5 := rfl

theorem S1717Five_eq_S1715Five : S1717Five = S1715Five := rfl

/-- The residue-characteristic half of Definition 3.1(c) at an arbitrary
actual place: l is prime to the residue characteristic of the place. -/
def S1717LTorsionCompatible (place : NumberField.FinitePlace S1687Field)
    (l : PrimeGeFive) : Prop :=
  Nat.Coprime l.value (NumberFieldFinitePlace.residueCharacteristic place)

/-- A place with residue characteristic r and l != r is compatible. -/
theorem S1717LTorsionCompatible_of_ne
    (place : NumberField.FinitePlace S1687Field) (l : PrimeGeFive) (r : Nat)
    (hr : NumberFieldFinitePlace.residueCharacteristic place = r)
    (hprime : Nat.Prime r) (hne : l.value ≠ r) :
    S1717LTorsionCompatible place l := by
  unfold S1717LTorsionCompatible
  rw [hr]
  exact (Nat.coprime_primes l.prime hprime).mpr hne

/-- The generic bad-place data for the D5 clause: an actual place, split
multiplicative reduction there, odd residue characteristic, and the explicit
numerical residue characteristic with its defining equality. -/
structure S1717D5PlaceData (l : PrimeGeFive) where
  place : NumberField.FinitePlace S1687Field
  splitMultiplicative : S1715Curve.HasSplitMultiplicativeReductionAt place
  odd_residueCharacteristic :
    Odd (NumberFieldFinitePlace.residueCharacteristic place)
  residueCharacteristic : Nat
  residueCharacteristic_eq : residueCharacteristic =
    NumberFieldFinitePlace.residueCharacteristic place
  lTorsionCompatible : Nat.Coprime l.value residueCharacteristic

/-- The generic D5 source clause, parameterized by the actual bad-place data
and the explicit source input S1715ImageContainsSL2 l.  The carrier,
label, absolute Galois group, mod-l representation and its surjectivity, and
the six-torsion statement are the actual S1715 objects.  The only
conditional field is the explicit SL_2 image statement. -/
noncomputable def S1717SourceTorsionClause (l : PrimeGeFive)
    (D : S1717D5PlaceData l) (hI : S1715ImageContainsSL2 l) :
    SourceTorsionClause.{0, 0, 0} l where
  torsionCarrier := S1715SixTorsionCarrier
  torsionCarrierLaw := inferInstance
  torsionLabel := S1715SixTorsionLabel
  torsionNonempty := ⟨1⟩
  representationCarrier := S1715AbsoluteGalois
  representationCarrierLaw := inferInstance
  representationGroup := S1715RepresentationGroup l
  representationGroupLaw := inferInstance
  representation := S1715Representation l
  representation_surjective := S1715Representation_surjective l
  imageContainsSL2 := S1715ImageContainsSL2 l
  imageContainsSL2_proved := hI
  sixTorsionIndependent := S1715SixTorsionIndependent
  sixTorsionIndependent_proved := S1715SixTorsionIndependent_proved
  lTorsionCompatible := Nat.Coprime l.value D.residueCharacteristic
  lTorsionCompatible_proved := D.lTorsionCompatible

@[simp] theorem S1717SourceTorsionClause_torsionCarrier (l : PrimeGeFive)
    (D : S1717D5PlaceData l) (hI : S1715ImageContainsSL2 l) :
    (S1717SourceTorsionClause l D hI).torsionCarrier =
      S1715SixTorsionCarrier := rfl

@[simp] theorem S1717SourceTorsionClause_torsionLabel (l : PrimeGeFive)
    (D : S1717D5PlaceData l) (hI : S1715ImageContainsSL2 l) :
    (S1717SourceTorsionClause l D hI).torsionLabel =
      S1715SixTorsionLabel := rfl

@[simp] theorem S1717SourceTorsionClause_representationCarrier
    (l : PrimeGeFive) (D : S1717D5PlaceData l)
    (hI : S1715ImageContainsSL2 l) :
    (S1717SourceTorsionClause l D hI).representationCarrier =
      S1715AbsoluteGalois := rfl

@[simp] theorem S1717SourceTorsionClause_representationGroup
    (l : PrimeGeFive) (D : S1717D5PlaceData l)
    (hI : S1715ImageContainsSL2 l) :
    (S1717SourceTorsionClause l D hI).representationGroup =
      S1715RepresentationGroup l := rfl

@[simp] theorem S1717SourceTorsionClause_representation
    (l : PrimeGeFive) (D : S1717D5PlaceData l)
    (hI : S1715ImageContainsSL2 l) :
    (S1717SourceTorsionClause l D hI).representation =
      S1715Representation l := rfl

@[simp] theorem S1717SourceTorsionClause_imageContainsSL2
    (l : PrimeGeFive) (D : S1717D5PlaceData l)
    (hI : S1715ImageContainsSL2 l) :
    (S1717SourceTorsionClause l D hI).imageContainsSL2 =
      S1715ImageContainsSL2 l := rfl

@[simp] theorem S1717SourceTorsionClause_sixTorsionIndependent
    (l : PrimeGeFive) (D : S1717D5PlaceData l)
    (hI : S1715ImageContainsSL2 l) :
    (S1717SourceTorsionClause l D hI).sixTorsionIndependent =
      PuncturedEllipticCurve.Torsion23Rational S1715Curve := rfl

@[simp] theorem S1717SourceTorsionClause_lTorsionCompatible
    (l : PrimeGeFive) (D : S1717D5PlaceData l)
    (hI : S1715ImageContainsSL2 l) :
    (S1717SourceTorsionClause l D hI).lTorsionCompatible =
      Nat.Coprime l.value D.residueCharacteristic := rfl

/-- The clause's lTorsionCompatible field is literally the actual
residue-characteristic condition at the chosen place. -/
theorem S1717SourceTorsionClause_lTorsionCompatible_place
    (l : PrimeGeFive) (D : S1717D5PlaceData l)
    (hI : S1715ImageContainsSL2 l) :
    (S1717SourceTorsionClause l D hI).lTorsionCompatible ↔
      S1717LTorsionCompatible D.place l := by
  rw [S1717SourceTorsionClause_lTorsionCompatible,
    S1717LTorsionCompatible, D.residueCharacteristic_eq]

/-- The clause's representation is the actual mod-l representation, hence
surjective onto its range. -/
theorem S1717SourceTorsionClause_representation_surjective
    (l : PrimeGeFive) (D : S1717D5PlaceData l)
    (hI : S1715ImageContainsSL2 l) :
    Function.Surjective (S1717SourceTorsionClause l D hI).representation :=
  (S1717SourceTorsionClause l D hI).representation_surjective

/-- The actual bad-place data at 7 for l = 5: place above 7, split
multiplicative reduction, odd residue characteristic 7, and coprimality of
5 and 7. -/
def S1717PlaceSevenD5Data : S1717D5PlaceData S1717Five where
  place := S1687PlaceAboveSeven
  splitMultiplicative := S1717SplitAtPlaceSeven
  odd_residueCharacteristic := S1717OddResidue_placeAboveSeven
  residueCharacteristic := 7
  residueCharacteristic_eq := S1717ResidueCharacteristic_placeAboveSeven.symm
  lTorsionCompatible := by
    simpa [S1717Five] using
      (Nat.coprime_primes Nat.prime_five Nat.prime_seven).mpr
        (by norm_num : (5 : Nat) ≠ 7)

@[simp] theorem S1717PlaceSevenD5Data_place :
    S1717PlaceSevenD5Data.place = S1687PlaceAboveSeven := rfl

@[simp] theorem S1717PlaceSevenD5Data_residueCharacteristic :
    S1717PlaceSevenD5Data.residueCharacteristic = 7 := rfl

/-- The actual l = 5 D5 clause, conditional only on the explicit image
input.  The bad place used is the actual place above 7. -/
noncomputable def S1717SourceTorsionClauseAtFive
    (hI : S1715ImageContainsSL2 S1717Five) :
    SourceTorsionClause.{0, 0, 0} S1717Five :=
  S1717SourceTorsionClause S1717Five S1717PlaceSevenD5Data hI

@[simp] theorem S1717SourceTorsionClauseAtFive_torsionCarrier
    (hI : S1715ImageContainsSL2 S1717Five) :
    (S1717SourceTorsionClauseAtFive hI).torsionCarrier =
      S1715SixTorsionCarrier := rfl

@[simp] theorem S1717SourceTorsionClauseAtFive_sixTorsionIndependent
    (hI : S1715ImageContainsSL2 S1717Five) :
    (S1717SourceTorsionClauseAtFive hI).sixTorsionIndependent =
      PuncturedEllipticCurve.Torsion23Rational S1715Curve := rfl

/-- The l = 5 clause's compatibility field is the explicit coprimality of 5
and 7. -/
theorem S1717SourceTorsionClauseAtFive_lTorsionCompatible
    (hI : S1715ImageContainsSL2 S1717Five) :
    (S1717SourceTorsionClauseAtFive hI).lTorsionCompatible =
      Nat.Coprime 5 7 := rfl

/-- The l = 5 clause's compatibility field is the actual residue
characteristic condition at the place above 7. -/
theorem S1717SourceTorsionClauseAtFive_lTorsionCompatible_actual
    (hI : S1715ImageContainsSL2 S1717Five) :
    (S1717SourceTorsionClauseAtFive hI).lTorsionCompatible =
      S1717LTorsionCompatible S1687PlaceAboveSeven S1717Five := by
  rw [S1717SourceTorsionClauseAtFive_lTorsionCompatible]
  unfold S1717LTorsionCompatible
  rw [S1717ResidueCharacteristic_placeAboveSeven]
  rfl

/-- The compatibility condition at the place above 7 holds for l = 5. -/
theorem S1717LTorsionCompatible_five_placeSeven :
    S1717LTorsionCompatible S1687PlaceAboveSeven S1717Five := by
  unfold S1717LTorsionCompatible
  rw [S1717ResidueCharacteristic_placeAboveSeven]
  exact (Nat.coprime_primes Nat.prime_five Nat.prime_seven).mpr
    (by norm_num : (5 : Nat) ≠ 7)

/-- The l = 5 clause supplies all three source-clause fields. -/
theorem S1717SourceTorsionClauseAtFive_fields
    (hI : S1715ImageContainsSL2 S1717Five) :
    (S1717SourceTorsionClauseAtFive hI).imageContainsSL2 ∧
      (S1717SourceTorsionClauseAtFive hI).sixTorsionIndependent ∧
      (S1717SourceTorsionClauseAtFive hI).lTorsionCompatible :=
  ⟨hI, S1715SixTorsionIndependent_proved,
    (S1717SourceTorsionClauseAtFive hI).lTorsionCompatible_proved⟩

/-- Conditional existence of the actual l = 5 clause from the explicit image
input. -/
theorem S1717D5_exists_at_five
    (hI : S1715ImageContainsSL2 S1717Five) :
    ∃ T : SourceTorsionClause.{0, 0, 0} S1717Five,
      T.torsionCarrier = S1715SixTorsionCarrier ∧
      T.sixTorsionIndependent =
        PuncturedEllipticCurve.Torsion23Rational S1715Curve ∧
      T.lTorsionCompatible = Nat.Coprime 5 7 :=
  ⟨S1717SourceTorsionClauseAtFive hI, rfl, rfl, rfl⟩

/-- The l = 5 clause's condition is exactly the residue-characteristic
condition at place 7. -/
theorem S1717D5_exists_at_five_place_condition
    (hI : S1715ImageContainsSL2 S1717Five) :
    ∃ T : SourceTorsionClause.{0, 0, 0} S1717Five,
      T.lTorsionCompatible =
        S1717LTorsionCompatible S1687PlaceAboveSeven S1717Five :=
  ⟨S1717SourceTorsionClauseAtFive hI,
    S1717SourceTorsionClauseAtFive_lTorsionCompatible_actual hI⟩

/-- The S1715 clause at l = 5 with the actual place above 5 is impossible:
its compatibility field would be the false coprimality of 5 with 5.  The new
clause avoids this by using place 7. -/
theorem S1717NoS1715ClauseAtFive :
    ¬ ∃ T : SourceTorsionClause.{0, 0, 0} S1717Five,
        T.lTorsionCompatible = S1715LTorsionCompatible S1715Five := by
  simpa [S1717Five] using S1715NoActualClauseAtFive

/-- The l = 5 clause is built from place 7, not from the place above 5. -/
theorem S1717FiveClause_uses_place_seven :
    S1717PlaceSevenD5Data.place = S1687PlaceAboveSeven := rfl

/-! ## 6. Admissibility still uses place 5; only D5 moves to place 7 -/

/-- The actual S1667 admissible-curve statement, via S1715/S1714.  This does
not involve place 7. -/
theorem S1717Admissible : S1667Admissible :=
  S1715Admissible

/-- The realization datum used for admissibility is the one whose place is
the actual place above 5. -/
theorem S1717Admissible_place_five :
    (S1712RealizationData S1714Split).place = S1687PlaceAboveFive := rfl

/-- The admissibility place (above 5) and the D5 bad place (above 7) are
distinct.  The l = 5 obstruction is removed without moving the place used
for admissibility. -/
theorem S1717PlaceAboveSeven_ne_placeAboveFive :
    S1687PlaceAboveSeven ≠ S1687PlaceAboveFive := by
  intro h
  have hc := congrArg (NumberFieldFinitePlace.comap (k := ℚ)) h
  rw [S1687PlaceAboveSeven_comap, S1687PlaceAboveFive_comap] at hc
  have h7 := congrArg NumberFieldFinitePlace.residueCharacteristic hc
  rw [concreteSevenPlace_residueCharacteristic,
    S1712ConcreteFivePlace_residueCharacteristic] at h7
  norm_num at h7

/-- The complete l = 5 configuration: S1667Admissible is proved using the
place above 5, while the D5 clause uses the distinct place above 7, where
the curve has split multiplicative reduction and odd residue
characteristic 7. -/
theorem S1717FiveConfiguration :
    S1667Admissible ∧
      (S1712RealizationData S1714Split).place = S1687PlaceAboveFive ∧
      S1687PlaceAboveSeven ≠ S1687PlaceAboveFive ∧
      S1715Curve.HasSplitMultiplicativeReductionAt S1687PlaceAboveSeven ∧
      Odd (NumberFieldFinitePlace.residueCharacteristic
        S1687PlaceAboveSeven) ∧
      S1717LTorsionCompatible S1687PlaceAboveSeven S1717Five :=
  ⟨S1717Admissible, rfl, S1717PlaceAboveSeven_ne_placeAboveFive,
    S1717SplitAtPlaceSeven, S1717OddResidue_placeAboveSeven,
    S1717LTorsionCompatible_five_placeSeven⟩

/-- The D5 clause at l = 5, with the exact remaining input made explicit:
the only hypothesis is the literal SL_2 containment for the actual curve. -/
theorem S1717D5_at_five_conditional :
    S1715ImageContainsSL2 S1717Five →
      ∃ T : SourceTorsionClause.{0, 0, 0} S1717Five,
        T.lTorsionCompatible =
          S1717LTorsionCompatible S1687PlaceAboveSeven S1717Five :=
  S1717D5_exists_at_five_place_condition

/-! ## 7. Axiom footprint -/

#print axioms S1717Curve_delta_seven_valuation_eq_two
#print axioms S1717Curve_c4_seven_valuation_eq_zero
#print axioms two_X_sq_add_five_discriminant
#print axioms two_X_sq_add_five_roots
#print axioms concreteSevenPlace_residueCharacteristic
#print axioms S1717_splitMultiplicativeReductionAtSeven
#print axioms S1687PlaceAboveSeven_comap
#print axioms S1717SplitAtPlaceSeven
#print axioms S1717ResidueCharacteristic_placeAboveSeven
#print axioms S1717LTorsionCompatible_five_placeSeven
#print axioms S1717SourceTorsionClause
#print axioms S1717SourceTorsionClauseAtFive
#print axioms S1717SourceTorsionClauseAtFive_fields
#print axioms S1717D5_exists_at_five
#print axioms S1717NoS1715ClauseAtFive
#print axioms S1717Admissible
#print axioms S1717Admissible_place_five
#print axioms S1717PlaceAboveSeven_ne_placeAboveFive
#print axioms S1717FiveConfiguration

end LeanFormal.IUT.XiFPaper.S1717PlaceSevenD5Actual