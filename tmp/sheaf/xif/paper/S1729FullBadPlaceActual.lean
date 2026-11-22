import tmp.sheaf.xif.paper.S1724PaperArithmeticActual
import tmp.sheaf.xif.paper.S1717PlaceSevenD5Actual
import tmp.sheaf.xif.paper.S1711RationalSplitAtFiveBridge
import tmp.sheaf.xif.paper.S1712OddResidueActual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction

/-!
# S1729: the complete bad-place selection for the S1667 curve over F'

S1720 constructs the actual field F' = SplittingField (S1687H * (X^2+1)),
the base-changed punctured curve E' = S1667Punctured.baseChange F', and the
actual finite places of F' above the rational places 5 and 7, with split
multiplicative reduction there.  S1724 gives the unconditional actual
arithmetic input A l = S1724InitialThetaArithmeticData l
(A.Fmod = Q, A.F = A.K = F').

This file completes the bad-place side at the level of the actual S1667
curve and its field F':

* **The third rational bad place.**  `concreteThreePlace` is the actual
  rational finite place at 3, built from Mathlib's height-one-prime data
  exactly as `concreteFivePlace` / `concreteSevenPlace`.  Its residue
  characteristic is proved to be 3.
* **Split multiplicative reduction at 3.**  The integral model over Z_3
  with a_2 = 61/64 and a_4 = -125/64 (both 3-adic units) has
  c_4 = 27721/256 a 3-adic unit and v_3(Delta) = 6; its reduction is
  y^2 = x^3 + x^2 + x over F_3, with c_4 = 1, Delta = 0 and tangent
  polynomial splitReductionPolynomial = T^2 - 1, which splits.  Hence
  split multiplicative reduction of the actual completion and of the global
  punctured curve at `concreteThreePlace`.  The split tangent polynomial is
  computed explicitly (not postulated).
* **The q-parameter 3^{-6} (type I6).**  `S1729QParameter 3 6 = (1/3)^6` is a
  real, nonzero, contracting parameter; v_3(Delta) = 6 is proved from the
  explicit factorization Delta = 3^6 * 5^6 * 7^2 / 2^20, and the 3-adic norm
  of Delta is proved to be 3^{-6}.
* **The actual place above 3 in F'.**  `S1729PlaceAboveThree` is obtained from
  the actual lying-over surjectivity (comap_surjective) with
  comap = concreteThreePlace, and split multiplicative reduction transports
  to it by the base-change theorem.
* **The full bad moduli set.**  `S1729VModBad = {3, 5, 7}` is a three-element
  set of actual rational places (explicitly not a singleton): the three
  places are pairwise distinct, each has odd residue characteristic, and the
  set is nonempty.  From it the actual SourcePlaceSelection A l is
  constructed (`S1729Selection`).
* **Clause (b) cards for all three places.**  `S1729BadPlaceReductionCards l`
  proves stable, multiplicative and split multiplicative reduction at every
  place of F' above any of the three bad moduli places, by base change from
  the three rational places.
* **Clause (c) cards.**  `S1729QParameterCards l` is constructed under the
  exact source hypothesis `S1729LTorsionCompatible l` (the residue
  characteristics 3, 5, 7 are prime to l), with the type-I orders 6, 6, 2
  (the exponents of Delta at 3, 5, 7).  This hypothesis is equivalent to
  l.value != 5 and l.value != 7 for l >= 5; at l = 5 and l = 7 the card is
  *refuted*, so those are exactly the missing values of l for the literal
  full set {3,5,7} (the paper's condition (c) forces the fixed l to be
  outside the bad moduli set).  The assembly into the Theorem 3.11 reduction
  clause is `S1729SourceReductionClause`.

No sorry, no axiom, no True/PUnit placeholder, no singleton posing as the full
bad set.  The only conditional input is `S1729LTorsionCompatible l`, recorded
as a proposition and proved to be exactly l != 5 /\ l != 7.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1729FullBadPlaceActual

open Polynomial WeierstrassCurve
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1724PaperArithmeticActual
open LeanFormal.IUT.XiFPaper.S1717PlaceSevenD5Actual
open LeanFormal.IUT.XiFPaper.S1712OddResidueActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

/-! ## 1. The actual rational finite place at 3 -/

/-- The rational local field at 3. -/
abbrev K3 := ℚ_[3]

/-- The 3-adic integers. -/
abbrev R3 := ℤ_[3]

def concreteThreePrime : Nat.Primes :=
  ⟨3, Nat.prime_three⟩

def concreteThreeHeightOne :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm
    concreteThreePrime

/-- The actual rational finite place at the prime 3. -/
def concreteThreePlace : NumberField.FinitePlace ℚ :=
  NumberField.FinitePlace.mk concreteThreeHeightOne

@[simp] theorem concreteThreePlace_maximalIdeal :
    concreteThreePlace.maximalIdeal = concreteThreeHeightOne := by
  exact NumberField.FinitePlace.maximalIdeal_mk concreteThreeHeightOne

@[simp] theorem concreteThreePlace_underlyingPrime :
    NumberFieldFinitePlace.underlyingPrime concreteThreePlace =
      concreteThreeHeightOne := by
  exact concreteThreePlace_maximalIdeal

theorem concreteThreeHeightOne_natGenerator :
    Rat.HeightOneSpectrum.natGenerator concreteThreeHeightOne = 3 := by
  exact congrArg (fun p : Nat.Primes => p.1)
    ((Rat.HeightOneSpectrum.primesEquiv
      (R := NumberField.RingOfIntegers ℚ)).apply_symm_apply concreteThreePrime)

theorem concreteThreeHeightOne_three_mem :
    (3 : NumberField.RingOfIntegers ℚ) ∈ concreteThreeHeightOne.asIdeal := by
  apply (Ideal.apply_mem_of_equiv_iff
    (I := concreteThreeHeightOne.asIdeal)
    (f := Rat.IsIntegralClosure.intEquiv
      (NumberField.RingOfIntegers ℚ))).mp
  have hdiv : Rat.HeightOneSpectrum.natGenerator concreteThreeHeightOne ∣ 3 := by
    rw [concreteThreeHeightOne_natGenerator]
  have hmap :=
    (Rat.HeightOneSpectrum.natGenerator_dvd_iff concreteThreeHeightOne).mp hdiv
  convert hmap using 1
  rw [Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv]
  exact map_intCast Rat.ringOfIntegersEquiv 3

/-- The height-one prime is the principal ideal generated by 3 in the
rational ring of integers. -/
theorem concreteThreeHeightOne_asIdeal_eq_span :
    concreteThreeHeightOne.asIdeal =
      Ideal.span {(3 : NumberField.RingOfIntegers ℚ)} := by
  let e : NumberField.RingOfIntegers ℚ ≃+* ℤ :=
    Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)
  have h := Rat.HeightOneSpectrum.span_natGenerator
    (R := NumberField.RingOfIntegers ℚ) concreteThreeHeightOne
  rw [concreteThreeHeightOne_natGenerator] at h
  change Ideal.span {(3 : ℤ)} =
    Ideal.map e.toRingHom concreteThreeHeightOne.asIdeal at h
  have h' := congrArg (Ideal.map e.symm.toRingHom) h
  rw [Ideal.map_span] at h'
  simp only [Set.image_singleton] at h'
  simp at h'
  exact h'.symm

/-- The residue characteristic of the rational place 3 is 3. -/
theorem concreteThreePlace_residueCharacteristic :
    NumberFieldFinitePlace.residueCharacteristic concreteThreePlace = 3 := by
  rw [NumberFieldFinitePlace.residueCharacteristic]
  change ringChar (NumberField.RingOfIntegers ℚ ⧸
    concreteThreePlace.maximalIdeal.asIdeal) = 3
  rw [concreteThreePlace_maximalIdeal, concreteThreeHeightOne_asIdeal_eq_span]
  rw [Ideal.ringChar_quot]
  have hunder : Ideal.under ℤ
      (Ideal.span {(3 : NumberField.RingOfIntegers ℚ)}) =
      Ideal.span {(3 : ℤ)} := by
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

abbrev concreteThreeCompletion := concreteThreeHeightOne.adicCompletion ℚ

/-- Pin the algebra structure on the completed field to the canonical
adic-completion structure; this avoids the generic division-ring instance
diamond with the field structure. -/
local instance : Algebra ℚ concreteThreeCompletion :=
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
    (NumberField.RingOfIntegers ℚ) ℚ concreteThreeHeightOne

abbrev concreteThreeCompletionIntegers :=
  concreteThreeHeightOne.adicCompletionIntegers ℚ

noncomputable def concreteThreePadicEquiv :
    K3 ≃A[ℚ] concreteThreeCompletion :=
  Padic.adicCompletionEquiv (R := NumberField.RingOfIntegers ℚ) concreteThreePrime

noncomputable def concreteThreePadicIntEquiv :
    R3 ≃A[ℤ] concreteThreeCompletionIntegers :=
  PadicInt.adicCompletionIntegersEquiv (R := NumberField.RingOfIntegers ℚ)
    concreteThreePrime

theorem concreteThreePadicEquiv_algebraMap (x : ℚ) :
    concreteThreePadicEquiv (algebraMap ℚ K3 x) =
      algebraMap ℚ concreteThreeCompletion x := by
  exact concreteThreePadicEquiv.commutes x

theorem concreteThreePadicIntEquiv_coe (x : R3) :
    (concreteThreePadicIntEquiv x : concreteThreeCompletion) =
      concreteThreePadicEquiv (x : K3) :=
  PadicInt.coe_adicCompletionIntegersEquiv_apply
    (R := NumberField.RingOfIntegers ℚ) concreteThreePrime x

/-! ## 2. Split multiplicative reduction of the S1667 curve at 3 -/

/-- 61/64 is a 3-adic unit. -/
lemma S1729_norm_61_64 : ‖(61 / 64 : K3)‖ = 1 := by
  rw [show (61 / 64 : K3) = ((61 : ℕ) : K3) / ((64 : ℕ) : K3) by norm_num]
  rw [norm_div]
  have h1 : ‖((61 : ℕ) : K3)‖ = 1 :=
    (Padic.norm_natCast_eq_one_iff (p := 3) (n := 61)).2 (by norm_num)
  have h2 : ‖((64 : ℕ) : K3)‖ = 1 :=
    (Padic.norm_natCast_eq_one_iff (p := 3) (n := 64)).2 (by norm_num)
  rw [h1, h2]
  norm_num

/-- -125/64 is a 3-adic unit (this is the difference from the place 5, where
-125/64 is a uniformizer; at 3 both coefficients are units). -/
lemma S1729_norm_neg125_64_eq_one : ‖(-125 / 64 : K3)‖ = 1 := by
  rw [show (-125 / 64 : K3) =
    ((-125 : ℤ) : K3) / ((64 : ℕ) : K3) by norm_num]
  rw [norm_div]
  have h1 : ‖((-125 : ℤ) : K3)‖ = 1 := by
    rw [Padic.norm_intCast_eq_one_iff]
    norm_num
  have h2 : ‖((64 : ℕ) : K3)‖ = 1 :=
    (Padic.norm_natCast_eq_one_iff (p := 3) (n := 64)).2 (by norm_num)
  rw [h1, h2, div_one]

/-- The lift of 61/64 to Z_3. -/
def S1729z2 : R3 := ⟨(61 / 64 : K3), le_of_eq S1729_norm_61_64⟩

/-- The lift of -125/64 to Z_3. -/
def S1729z4 : R3 := ⟨(-125 / 64 : K3), le_of_eq S1729_norm_neg125_64_eq_one⟩

/-- The explicit integral model of the S1667 curve at 3. -/
def S1729I0 : WeierstrassCurve R3 :=
  WeierstrassCurve.mk 0 S1729z2 0 S1729z4 0

lemma S1729z2_mul_64 : S1729z2 * (64 : R3) = (61 : R3) := by
  apply Subtype.ext
  change (61 / 64 : K3) * (64 : K3) = (61 : K3)
  norm_num

lemma S1729z4_mul_64 : S1729z4 * (64 : R3) = (-125 : R3) := by
  apply Subtype.ext
  change (-125 / 64 : K3) * (64 : K3) = (-125 : K3)
  norm_num

/-- The integral model base-changes to the completion of the S1667 curve. -/
theorem S1729I0_baseChange :
    S1729I0.map (algebraMap R3 K3) = S1667Curve.baseChange K3 := by
  ext <;> simp [S1729I0, S1729z2, S1729z4, S1667Curve, WeierstrassCurve.baseChange]

/-- The discriminant numerator is divisible by 3^6 but not 3^7, and the
denominator is prime to 3: v_3(Delta) = 6 for the S1667 discriminant. -/
theorem S1729Curve_delta_three_valuation_eq_six :
    S1667Curve.Δ = (558140625 / 1048576 : ℚ) ∧
      (3 ^ 6 : ℕ) ∣ 558140625 ∧
      ¬ ((3 ^ 7 : ℕ) ∣ 558140625) ∧
      ¬ ((3 : ℕ) ∣ 1048576) := by
  refine ⟨S1667Curve_Δ, by norm_num, by norm_num, by norm_num⟩

/-- The c_4 numerator 27721 and denominator 256 are both prime to 3, so
c_4 = 27721/256 is a 3-adic unit (v_3(c_4) = 0). -/
theorem S1729Curve_c4_three_valuation_eq_zero :
    S1667Curve.c₄ = (27721 / 256 : ℚ) ∧
      ¬ ((3 : ℕ) ∣ 27721) ∧
      ¬ ((3 : ℕ) ∣ 256) := by
  refine ⟨S1667Curve_c₄, by norm_num, by norm_num⟩

/-- The reduction of the integral model, over F_3. -/
def S1729J : WeierstrassCurve (ZMod 3) :=
  S1729I0.map (PadicInt.toZMod (p := 3))

lemma S1729toZMod_64 : PadicInt.toZMod (p := 3) (64 : R3) = 1 := by
  rw [show (64 : R3) = ((64 : ℕ) : R3) by norm_num]
  rw [map_natCast]
  decide

lemma S1729toZMod_61 : PadicInt.toZMod (p := 3) (61 : R3) = 1 := by
  rw [show (61 : R3) = ((61 : ℕ) : R3) by norm_num]
  rw [map_natCast]
  decide

lemma S1729toZMod_neg125 : PadicInt.toZMod (p := 3) (-125 : R3) = 1 := by
  rw [show (-125 : R3) = ((-125 : ℤ) : R3) by norm_num]
  rw [map_intCast]
  decide

lemma S1729toZMod_z2 : PadicInt.toZMod (p := 3) S1729z2 = 1 := by
  have hz : PadicInt.toZMod (p := 3) S1729z2 * (1 : ZMod 3) = 1 := by
    have h := congrArg (PadicInt.toZMod (p := 3)) S1729z2_mul_64
    rw [map_mul, S1729toZMod_64, S1729toZMod_61] at h
    exact h
  simpa using hz

lemma S1729toZMod_z4 : PadicInt.toZMod (p := 3) S1729z4 = 1 := by
  have hz : PadicInt.toZMod (p := 3) S1729z4 * (1 : ZMod 3) = 1 := by
    have h := congrArg (PadicInt.toZMod (p := 3)) S1729z4_mul_64
    rw [map_mul, S1729toZMod_64, S1729toZMod_neg125] at h
    exact h
  simpa using hz

lemma S1729J_eq : S1729J = WeierstrassCurve.mk (0 : ZMod 3) 1 0 1 0 := by
  ext <;> simp [S1729J, S1729I0, S1729toZMod_z2, S1729toZMod_z4]

lemma S1729J_c4 : S1729J.c₄ = (1 : ZMod 3) := by
  rw [S1729J_eq]
  decide

lemma S1729J_delta : S1729J.Δ = (0 : ZMod 3) := by
  rw [S1729J_eq]
  decide

lemma S1729J_a1 : S1729J.a₁ = (0 : ZMod 3) := by
  rw [S1729J_eq]

lemma S1729J_splitConstant :
    54 * S1729J.b₆ - 3 * S1729J.b₂ * S1729J.b₄ + S1729J.a₂ * S1729J.c₄ =
      (1 : ZMod 3) := by
  rw [S1729J_eq]
  decide

/-- The tangent polynomial of the reduced model is T^2 - 1. -/
lemma S1729J_splitReductionPolynomial :
    splitReductionPolynomial S1729J = (X ^ 2 - 1 : (ZMod 3)[X]) := by
  have hmain : splitReductionPolynomial S1729J = C 1 * X ^ 2 - C 1 := by
    rw [splitReductionPolynomial, S1729J_splitConstant, S1729J_c4, S1729J_a1]
    simp only [mul_zero, C_0, zero_mul, add_zero]
  rw [hmain]
  simp only [C_1, one_mul]

/-- T^2 - 1 = (T - 1)(T + 1) over F_3. -/
lemma S1729X_sq_sub_one_factor :
    (X ^ 2 - 1 : (ZMod 3)[X]) = (X - C 1) * (X + C 1) := by
  simp only [C_1]
  ring

/-- The tangent polynomial splits over the residue field F_3. -/
lemma S1729X_sq_sub_one_splits :
    (X ^ 2 - 1 : (ZMod 3)[X]).Splits := by
  rw [S1729X_sq_sub_one_factor]
  exact (Polynomial.Splits.X_sub_C 1).mul (Polynomial.Splits.X_add_C 1)

lemma S1729toZMod_I0_c4 : PadicInt.toZMod (p := 3) S1729I0.c₄ = 1 := by
  rw [← WeierstrassCurve.map_c₄ (f := PadicInt.toZMod (p := 3)) (W := S1729I0)]
  exact S1729J_c4

lemma S1729toZMod_I0_delta : PadicInt.toZMod (p := 3) S1729I0.Δ = 0 := by
  rw [← WeierstrassCurve.map_Δ (f := PadicInt.toZMod (p := 3)) (W := S1729I0)]
  exact S1729J_delta

lemma S1729I0_c4_notMem_maximalIdeal :
    S1729I0.c₄ ∉ IsLocalRing.maximalIdeal R3 := by
  rw [← PadicInt.ker_toZMod (p := 3)]
  intro h
  have hzero : PadicInt.toZMod (p := 3) S1729I0.c₄ = 0 := RingHom.mem_ker.mp h
  rw [S1729toZMod_I0_c4] at hzero
  exact (by decide : (1 : ZMod 3) ≠ 0) hzero

lemma S1729I0_delta_mem_maximalIdeal : S1729I0.Δ ∈ IsLocalRing.maximalIdeal R3 := by
  rw [← PadicInt.ker_toZMod (p := 3)]
  exact RingHom.mem_ker.mpr S1729toZMod_I0_delta

theorem S1729W3_isIntegral :
    WeierstrassCurve.IsIntegral R3 (S1667Curve.baseChange K3) :=
  ⟨⟨S1729I0, S1729I0_baseChange.symm⟩⟩

attribute [local instance] S1729W3_isIntegral

theorem S1729I0_integralModel_eq :
    (S1667Curve.baseChange K3).integralModel R3 = S1729I0 := by
  letI : WeierstrassCurve.IsIntegral R3 (S1667Curve.baseChange K3) :=
    S1729W3_isIntegral
  apply WeierstrassCurve.map_injective
    (FaithfulSMul.algebraMap_injective R3 K3)
  change ((S1667Curve.baseChange K3).integralModel R3).baseChange K3 =
    S1729I0.baseChange K3
  rw [WeierstrassCurve.baseChange_integralModel_eq]
  exact S1729I0_baseChange.symm

theorem S1729W3_c4_valuation :
    (IsDiscreteValuationRing.maximalIdeal R3).valuation K3
      (S1667Curve.baseChange K3).c₄ = 1 := by
  letI : WeierstrassCurve.IsIntegral R3 (S1667Curve.baseChange K3) :=
    S1729W3_isIntegral
  rw [← WeierstrassCurve.integralModel_c₄_eq R3 (S1667Curve.baseChange K3)]
  rw [S1729I0_integralModel_eq]
  exact ((IsDiscreteValuationRing.maximalIdeal R3).valuation_eq_one_iff_notMem
    (K := K3)).mpr S1729I0_c4_notMem_maximalIdeal

theorem S1729W3_delta_valuation_lt_one :
    (IsDiscreteValuationRing.maximalIdeal R3).valuation K3
      (S1667Curve.baseChange K3).Δ < 1 := by
  letI : WeierstrassCurve.IsIntegral R3 (S1667Curve.baseChange K3) :=
    S1729W3_isIntegral
  rw [← WeierstrassCurve.integralModel_Δ_eq R3 (S1667Curve.baseChange K3)]
  rw [S1729I0_integralModel_eq]
  exact ((IsDiscreteValuationRing.maximalIdeal R3).valuation_lt_one_iff_mem
    (K := K3) S1729I0.Δ).mpr S1729I0_delta_mem_maximalIdeal

theorem S1729W3_isMinimal :
    WeierstrassCurve.IsMinimal R3 (S1667Curve.baseChange K3) := by
  letI : WeierstrassCurve.IsIntegral R3 (S1667Curve.baseChange K3) :=
    S1729W3_isIntegral
  exact isMinimal_of_isIntegral_valuation_c₄_eq_one R3
    (S1667Curve.baseChange K3) S1729W3_c4_valuation

theorem S1729W3_hasMultiplicativeReduction :
    (S1667Curve.baseChange K3).HasMultiplicativeReduction R3 := by
  letI : WeierstrassCurve.IsIntegral R3 (S1667Curve.baseChange K3) :=
    S1729W3_isIntegral
  letI : WeierstrassCurve.IsMinimal R3 (S1667Curve.baseChange K3) :=
    S1729W3_isMinimal
  exact
    { badReduction := S1729W3_delta_valuation_lt_one
      multiplicativeReduction := S1729W3_c4_valuation }

theorem S1729W3_hasSplitMultiplicativeReduction :
    (S1667Curve.baseChange K3).HasSplitMultiplicativeReduction R3 := by
  letI : WeierstrassCurve.IsIntegral R3 (S1667Curve.baseChange K3) :=
    S1729W3_isIntegral
  letI : WeierstrassCurve.IsMinimal R3 (S1667Curve.baseChange K3) :=
    S1729W3_isMinimal
  letI : (S1667Curve.baseChange K3).HasMultiplicativeReduction R3 :=
    S1729W3_hasMultiplicativeReduction
  refine { splitMultiplicativeReduction := ?_ }
  rw [S1729I0_integralModel_eq]
  change Polynomial.Splits
    ((splitReductionPolynomial S1729I0).map
      (algebraMap R3 (IsLocalRing.ResidueField R3)))
  let P : (IsLocalRing.ResidueField R3)[X] :=
    (splitReductionPolynomial S1729I0).map (IsLocalRing.residue R3)
  let rf : IsLocalRing.ResidueField R3 ≃+* ZMod 3 :=
    PadicInt.residueField (p := 3)
  have hcomp : rf.toRingHom.comp (IsLocalRing.residue R3) =
      PadicInt.toZMod (p := 3) :=
    (PadicInt.toZMod_eq_residueField_comp_residue (p := 3)).symm
  have hP : P.map rf.toRingHom = (X ^ 2 - 1 : (ZMod 3)[X]) := by
    calc P.map rf.toRingHom
        = (splitReductionPolynomial S1729I0).map
            (rf.toRingHom.comp (IsLocalRing.residue R3)) := by
          simp only [P, Polynomial.map_map]
      _ = (splitReductionPolynomial S1729I0).map (PadicInt.toZMod (p := 3)) := by
          rw [hcomp]
      _ = splitReductionPolynomial S1729J := by
          rw [S1729J, splitReductionPolynomial_map]
      _ = (X ^ 2 - 1 : (ZMod 3)[X]) := S1729J_splitReductionPolynomial
  have hsplit : (P.map rf.toRingHom).Splits := by
    rw [hP]
    exact S1729X_sq_sub_one_splits
  exact Polynomial.Splits.of_splits_map rf.toRingHom hsplit
    (fun a _ => ⟨rf.symm a, by simp⟩)

/-! ## 3. The split reduction as a statement at the rational place 3 -/

/-- The punctured S1667 curve has split multiplicative reduction at the
actual rational place 3. -/
theorem S1729_splitMultiplicativeReductionAtThree :
    S1667Punctured.HasSplitMultiplicativeReductionAt concreteThreePlace := by
  have hW : HasSplitMultiplicativeReductionOnMinimalModel R3
      (S1667Curve.baseChange K3) :=
    ⟨1, by simpa using S1729W3_hasSplitMultiplicativeReduction⟩
  have hcomm :
      concreteThreePadicEquiv.toRingEquiv.toRingHom.comp (algebraMap R3 K3) =
      (algebraMap concreteThreeCompletionIntegers concreteThreeCompletion).comp
        concreteThreePadicIntEquiv.toRingEquiv.toRingHom := by
    apply RingHom.ext
    intro x
    dsimp only [RingHom.comp_apply]
    change concreteThreePadicEquiv
        (algebraMap R3 K3 x) =
      algebraMap concreteThreeCompletionIntegers concreteThreeCompletion
        (concreteThreePadicIntEquiv x)
    change concreteThreePadicEquiv
        (algebraMap R3 K3 x) =
      (concreteThreePadicIntEquiv x : concreteThreeCompletion)
    rw [concreteThreePadicIntEquiv_coe]
    congr 1
  letI : IsLocalHom concreteThreePadicIntEquiv.toRingEquiv.toRingHom := by
    refine ⟨fun x hx => ?_⟩
    simpa using hx.map concreteThreePadicIntEquiv.toRingEquiv.symm.toMonoidHom
  have hmap := hasSplitMultiplicativeReductionOnMinimalModel_map_of_commutes
    (R := R3) (S := concreteThreeCompletionIntegers)
    (K := K3) (L := concreteThreeCompletion)
    concreteThreePadicIntEquiv.toRingEquiv.toRingHom
    concreteThreePadicEquiv.toRingEquiv.toRingHom
    hcomm (S1667Curve.baseChange K3) hW
  have hWmap :
      (S1667Curve.baseChange K3).map concreteThreePadicEquiv.toRingEquiv.toRingHom =
      S1667Curve.baseChange concreteThreeCompletion := by
    have hcomp :
        concreteThreePadicEquiv.toRingEquiv.toRingHom.comp
          (algebraMap ℚ K3) =
        algebraMap ℚ concreteThreeCompletion := by
      apply RingHom.ext
      intro q
      exact concreteThreePadicEquiv_algebraMap q
    change S1667Curve.map
        (concreteThreePadicEquiv.toRingEquiv.toRingHom.comp
          (algebraMap ℚ K3)) =
      S1667Curve.map (algebraMap ℚ concreteThreeCompletion)
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
      concreteThreePlace_underlyingPrime.symm
      (by
        change HasSplitMultiplicativeReductionOnMinimalModel
          concreteThreeCompletionIntegers
          (S1667Curve.baseChange concreteThreeCompletion)
        exact hmap)
  simpa [F, S1667Punctured] using htransport

/-! ## 4. The actual place of F' above 3 -/

/-- An actual finite place of F' above the rational place 3, obtained from the
actual lying-over surjectivity. -/
noncomputable def S1729PlaceAboveThree : NumberField.FinitePlace S1720Field :=
  Classical.choose
    (NumberFieldFinitePlace.comap_surjective
      (k := ℚ) (K := S1720Field) concreteThreePlace)

/-- The place above 3 contracts to the rational place 3. -/
theorem S1729PlaceAboveThree_comap :
    NumberFieldFinitePlace.comap (k := ℚ) S1729PlaceAboveThree =
      concreteThreePlace :=
  Classical.choose_spec
    (NumberFieldFinitePlace.comap_surjective
      (k := ℚ) (K := S1720Field) concreteThreePlace)

/-- The actual place of F' above 3, under the name used by the S1720
interface requested by the task. -/
noncomputable abbrev S1720PlaceAboveThree : NumberField.FinitePlace S1720Field :=
  S1729PlaceAboveThree

/-- The S1720-named place above 3 contracts to the rational place 3. -/
theorem S1720PlaceAboveThree_comap :
    NumberFieldFinitePlace.comap (k := ℚ) S1720PlaceAboveThree =
      concreteThreePlace :=
  S1729PlaceAboveThree_comap

/-- The residue characteristic of the actual place above 3 is 3. -/
theorem S1729PlaceAboveThree_residueCharacteristic :
    NumberFieldFinitePlace.residueCharacteristic S1729PlaceAboveThree = 3 := by
  have h := NumberFieldFinitePlace.residueCharacteristic_comap
    (k := ℚ) (K := S1720Field) S1729PlaceAboveThree
  rw [S1729PlaceAboveThree_comap] at h
  rw [← h, concreteThreePlace_residueCharacteristic]

/-- The actual place above 3 has odd residue characteristic. -/
theorem S1729PlaceAboveThree_odd :
    Odd (NumberFieldFinitePlace.residueCharacteristic S1729PlaceAboveThree) := by
  rw [S1729PlaceAboveThree_residueCharacteristic]
  exact ⟨1, by norm_num⟩

/-- E' has split multiplicative reduction at the actual place above 3. -/
theorem S1729SplitAtPlaceAboveThree (l : PrimeGeFive) :
    (S1724InitialThetaArithmeticData l).curve.HasSplitMultiplicativeReductionAt
      S1729PlaceAboveThree := by
  apply PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_baseChange
    (k := ℚ) (K := S1720Field) S1667Punctured
  rw [S1729PlaceAboveThree_comap]
  exact S1729_splitMultiplicativeReductionAtThree

/-! ## 5. The q-parameter 3^{-6} (type I6) -/

/-- The real q-parameter (1/p)^n attached to a type-I_n place of residue
characteristic p. -/
def S1729QParameter (p n : ℕ) : ℝ :=
  ((p : ℝ)⁻¹) ^ n

theorem S1729QParameter_eq (p n : ℕ) :
    S1729QParameter p n = ((p : ℝ)⁻¹) ^ n := rfl

theorem S1729QParameter_ne_zero (p n : ℕ) (hp : p ≠ 0) :
    S1729QParameter p n ≠ 0 :=
  pow_ne_zero _ (inv_ne_zero (Nat.cast_ne_zero.mpr hp))

theorem S1729QParameter_nonneg (p n : ℕ) : 0 ≤ S1729QParameter p n :=
  pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p)) _

theorem S1729QParameter_norm (p n : ℕ) :
    ‖S1729QParameter p n‖ = ((p : ℝ)⁻¹) ^ n :=
  Real.norm_of_nonneg (S1729QParameter_nonneg p n)

theorem S1729QParameter_norm_lt_one (p n : ℕ) (hp : 1 < p) (hn : 0 < n) :
    ‖S1729QParameter p n‖ < 1 := by
  rw [S1729QParameter_norm]
  have hbase_nonneg : 0 ≤ ((p : ℝ)⁻¹) := inv_nonneg.mpr (Nat.cast_nonneg p)
  have hbase_lt_one : ((p : ℝ)⁻¹) < 1 := by
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast hp
  exact pow_lt_one₀ hbase_nonneg hbase_lt_one (Nat.ne_of_gt hn)

theorem S1729QParameter_ne_one (p n : ℕ) (hp : 1 < p) (hn : 0 < n) :
    S1729QParameter p n ≠ 1 := by
  intro h
  have hlt := S1729QParameter_norm_lt_one p n hp hn
  rw [h, norm_one] at hlt
  exact lt_irrefl 1 hlt

/-- The q-parameter at the place 3: 3^{-6}, the type-I_6 parameter. -/
def S1729Q : ℝ := S1729QParameter 3 6

theorem S1729Q_eq_inv_six : S1729Q = ((3 : ℝ)⁻¹) ^ 6 := rfl

theorem S1729Q_ne_zero : S1729Q ≠ 0 :=
  S1729QParameter_ne_zero 3 6 (by norm_num)

theorem S1729Q_norm : ‖S1729Q‖ = ((3 : ℝ)⁻¹) ^ 6 :=
  S1729QParameter_norm 3 6

theorem S1729Q_norm_lt_one : ‖S1729Q‖ < 1 :=
  S1729QParameter_norm_lt_one 3 6 (by norm_num) (by norm_num)

theorem S1729Q_ne_one : S1729Q ≠ 1 :=
  S1729QParameter_ne_one 3 6 (by norm_num) (by norm_num)

/-- The q-parameter equals the inverse of the residue characteristic of the
place above 3, raised to the valuation exponent 6. -/
theorem S1729Q_eq_residueCharacteristic :
    S1729Q =
      ((NumberFieldFinitePlace.residueCharacteristic
          S1729PlaceAboveThree : ℕ) : ℝ)⁻¹ ^ 6 := by
  rw [S1729PlaceAboveThree_residueCharacteristic]
  norm_num [S1729Q, S1729QParameter]

/-- The 3-adic norm of the S1667 discriminant is exactly 3^{-6}: the
valuation-theoretic content of type I_6 at the place 3. -/
theorem S1729Delta_norm_three :
    ‖(S1667Curve.Δ : K3)‖ = ((3 : ℝ)⁻¹) ^ 6 := by
  have hΔ : ((S1667Curve.Δ : ℚ) : K3) =
      ((558140625 : ℕ) : K3) / ((1048576 : ℕ) : K3) := by
    rw [S1667Curve_Δ]
    push_cast
    norm_num
  rw [hΔ, norm_div]
  have hnum : ((558140625 : ℕ) : K3) =
      ((3 : ℕ) : K3) ^ 6 * ((5 : ℕ) : K3) ^ 6 * ((7 : ℕ) : K3) ^ 2 := by
    norm_num
  have hden : ((1048576 : ℕ) : K3) = ((2 : ℕ) : K3) ^ 20 := by
    norm_num
  rw [hnum, hden]
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, norm_pow]
  have h3 : ‖((3 : ℕ) : K3)‖ = ((3 : ℝ)⁻¹) := by
    simpa using Padic.norm_p (p := 3)
  have h5 : ‖((5 : ℕ) : K3)‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    norm_num
  have h7 : ‖((7 : ℕ) : K3)‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    norm_num
  have h2 : ‖((2 : ℕ) : K3)‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    norm_num
  rw [h3, h5, h7, h2]
  norm_num

/-- The actual q-parameter data at the place above 3: a real, nonzero,
contracting, non-unit parameter 3^{-6}, the type-I_6 discriminant norm, and
the actual split multiplicative reduction of E' there. -/
structure S1729ThreeQData (l : PrimeGeFive) where
  q : ℝ
  q_eq : q = S1729Q
  q_ne_zero : q ≠ 0
  q_contracting : ‖q‖ < 1
  q_ne_one : q ≠ 1
  delta_norm : ‖(S1667Curve.Δ : K3)‖ = ((3 : ℝ)⁻¹) ^ 6
  splitReduction :
    (S1724InitialThetaArithmeticData l).curve.HasSplitMultiplicativeReductionAt
      S1729PlaceAboveThree

/-- The actual type-I_6 q-parameter data at the place above 3. -/
noncomputable def S1729ThreeQDataActual (l : PrimeGeFive) :
    S1729ThreeQData l where
  q := S1729Q
  q_eq := rfl
  q_ne_zero := S1729Q_ne_zero
  q_contracting := S1729Q_norm_lt_one
  q_ne_one := S1729Q_ne_one
  delta_norm := S1729Delta_norm_three
  splitReduction := S1729SplitAtPlaceAboveThree l

/-! ## 6. The full bad moduli set {3, 5, 7} and the source place selection -/

/-- The full bad moduli set of the S1667 curve at the rational places
3, 5 and 7. -/
def S1729VModBad : Set (NumberField.FinitePlace ℚ) :=
  {concreteThreePlace, concreteFivePlace, concreteSevenPlace}

theorem S1729VModBad_mem_iff (p : NumberField.FinitePlace ℚ) :
    p ∈ S1729VModBad ↔
      p = concreteThreePlace ∨ p = concreteFivePlace ∨
        p = concreteSevenPlace := by
  simp [S1729VModBad]

theorem S1729VModBad_three_mem : concreteThreePlace ∈ S1729VModBad := by
  simp [S1729VModBad]

theorem S1729VModBad_five_mem : concreteFivePlace ∈ S1729VModBad := by
  simp [S1729VModBad]

theorem S1729VModBad_seven_mem : concreteSevenPlace ∈ S1729VModBad := by
  simp [S1729VModBad]

theorem S1729VModBad_nonempty : S1729VModBad.Nonempty :=
  ⟨concreteThreePlace, S1729VModBad_three_mem⟩

theorem S1729VModBad_finite : S1729VModBad.Finite := by
  unfold S1729VModBad
  exact ((Set.finite_singleton concreteSevenPlace).insert concreteFivePlace).insert
    concreteThreePlace

/-- The three bad moduli places are pairwise distinct. -/
theorem S1729Three_ne_five : concreteThreePlace ≠ concreteFivePlace := by
  intro h
  have hrc := congrArg NumberFieldFinitePlace.residueCharacteristic h
  rw [concreteThreePlace_residueCharacteristic,
    S1712ConcreteFivePlace_residueCharacteristic] at hrc
  exact absurd hrc (by norm_num)

theorem S1729Three_ne_seven : concreteThreePlace ≠ concreteSevenPlace := by
  intro h
  have hrc := congrArg NumberFieldFinitePlace.residueCharacteristic h
  rw [concreteThreePlace_residueCharacteristic,
    concreteSevenPlace_residueCharacteristic] at hrc
  exact absurd hrc (by norm_num)

theorem S1729Five_ne_seven : concreteFivePlace ≠ concreteSevenPlace := by
  intro h
  have hrc := congrArg NumberFieldFinitePlace.residueCharacteristic h
  rw [S1712ConcreteFivePlace_residueCharacteristic,
    concreteSevenPlace_residueCharacteristic] at hrc
  exact absurd hrc (by norm_num)

/-- The bad moduli set is explicitly not a singleton: it contains two
distinct actual places. -/
theorem S1729VModBad_not_singleton :
    ∃ p ∈ S1729VModBad, ∃ q ∈ S1729VModBad, p ≠ q :=
  ⟨concreteThreePlace, S1729VModBad_three_mem,
    concreteFivePlace, S1729VModBad_five_mem, S1729Three_ne_five⟩

/-- The three actual bad moduli places are distinct elements of the set. -/
theorem S1729VModBad_three_distinct :
    concreteThreePlace ∈ S1729VModBad ∧ concreteFivePlace ∈ S1729VModBad ∧
      concreteSevenPlace ∈ S1729VModBad ∧
      concreteThreePlace ≠ concreteFivePlace ∧
      concreteThreePlace ≠ concreteSevenPlace ∧
      concreteFivePlace ≠ concreteSevenPlace :=
  ⟨S1729VModBad_three_mem, S1729VModBad_five_mem, S1729VModBad_seven_mem,
    S1729Three_ne_five, S1729Three_ne_seven, S1729Five_ne_seven⟩

/-- Every bad moduli place has odd residue characteristic. -/
theorem S1729VModBad_odd (p : NumberField.FinitePlace ℚ)
    (hp : p ∈ S1729VModBad) :
    Odd (NumberFieldFinitePlace.residueCharacteristic p) := by
  rcases (S1729VModBad_mem_iff p).mp hp with rfl | rfl | rfl
  · rw [concreteThreePlace_residueCharacteristic]
    exact ⟨1, by norm_num⟩
  · rw [S1712ConcreteFivePlace_residueCharacteristic]
    exact ⟨2, by norm_num⟩
  · rw [concreteSevenPlace_residueCharacteristic]
    exact ⟨3, by norm_num⟩

/-- The Definition 3.1(b) source place selection with the full bad moduli set
{3, 5, 7} over the actual arithmetic input A l. -/
def S1729Selection (l : PrimeGeFive) :
    SourcePlaceSelection (S1724InitialThetaArithmeticData l) where
  V_mod_bad := S1729VModBad
  V_mod_bad_odd_residue_characteristic := S1729VModBad_odd
  V_mod_bad_nonempty := S1729VModBad_nonempty

@[simp] theorem S1729Selection_V_mod_bad (l : PrimeGeFive) :
    (S1729Selection l).V_mod_bad = S1729VModBad := rfl

/-- The bad moduli set of the actual selection is the full triple {3, 5, 7}. -/
theorem S1729Selection_V_mod_bad_triple (l : PrimeGeFive) :
    (S1729Selection l).V_mod_bad =
      ({concreteThreePlace, concreteFivePlace, concreteSevenPlace} :
        Set (NumberField.FinitePlace ℚ)) := rfl

theorem S1729Selection_odd (l : PrimeGeFive)
    (p : NumberField.FinitePlace (S1724InitialThetaArithmeticData l).Fmod)
    (hp : p ∈ (S1729Selection l).V_mod_bad) :
    Odd (NumberFieldFinitePlace.residueCharacteristic p) :=
  (S1729Selection l).V_mod_bad_odd_residue_characteristic p hp

theorem S1729Selection_nonempty (l : PrimeGeFive) :
    (S1729Selection l).V_mod_bad.Nonempty :=
  (S1729Selection l).V_mod_bad_nonempty

theorem S1729Selection_V_mod_bad_finite (l : PrimeGeFive) :
    (S1729Selection l).V_mod_bad.Finite := by
  rw [S1729Selection_V_mod_bad]
  exact S1729VModBad_finite

/-- Finiteness of the bad moduli index (Bad P is the subtype of V^bad_mod). -/
@[reducible] noncomputable def S1729BadFintype (l : PrimeGeFive) :
    Fintype (Bad (S1729Selection l)) :=
  (S1729Selection_V_mod_bad_finite l).fintype

instance S1729BadFintypeInstance (l : PrimeGeFive) :
    Fintype (Bad (S1729Selection l)) :=
  S1729BadFintype l

/-! ## 7. Clause (b): reduction cards for all three bad places -/

/-- Split multiplicative reduction of the S1667 curve at the rational place 5
(from S1713). -/
theorem S1729RationalSplitAtFive :
    S1667Punctured.HasSplitMultiplicativeReductionAt concreteFivePlace :=
  S1711RationalSplitAtFive

/-- Split multiplicative reduction of the S1667 curve at the rational place 7
(from S1717). -/
theorem S1729RationalSplitAtSeven :
    S1667Punctured.HasSplitMultiplicativeReductionAt concreteSevenPlace :=
  S1717_splitMultiplicativeReductionAtSeven

/-- Split multiplicative reduction at every rational place in the full bad
moduli set, by cases on membership. -/
theorem S1729SplitAtModuli (p : NumberField.FinitePlace ℚ)
    (hp : p ∈ S1729VModBad) :
    S1667Punctured.HasSplitMultiplicativeReductionAt p := by
  rcases (S1729VModBad_mem_iff p).mp hp with rfl | rfl | rfl
  · exact S1729_splitMultiplicativeReductionAtThree
  · exact S1729RationalSplitAtFive
  · exact S1729RationalSplitAtSeven

/-- Split multiplicative reduction at every place of F' above a bad moduli
place, by base change from the rational place. -/
theorem S1729SplitAtDF (l : PrimeGeFive)
    (w : NumberField.FinitePlace S1720Field)
    (hw : NumberFieldFinitePlace.comap (k := ℚ) w ∈ S1729VModBad) :
    (S1724InitialThetaArithmeticData l).curve.HasSplitMultiplicativeReductionAt w :=
  PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_baseChange
    (k := ℚ) (K := S1720Field) S1667Punctured w
    (S1729SplitAtModuli (NumberFieldFinitePlace.comap (k := ℚ) w) hw)

/-- Clause (b) reduction cards at all three bad places. -/
theorem S1729BadPlaceReductionCards (l : PrimeGeFive) :
    BadPlaceReductionCards (S1729Selection l) :=
  BadPlaceReductionCards.ofSplitMultiplicative
    (fun w hw => S1729SplitAtDF l w hw)

theorem S1729BadPlaceReductionCards_split (l : PrimeGeFive)
    (w : NumberField.FinitePlace (S1724InitialThetaArithmeticData l).F)
    (hw : NumberFieldFinitePlace.comap
      (k := (S1724InitialThetaArithmeticData l).Fmod) w ∈
        (S1729Selection l).V_mod_bad) :
    (S1724InitialThetaArithmeticData l).curve.HasSplitMultiplicativeReductionAt w :=
  (S1729BadPlaceReductionCards l).splitMultiplicativeReduction w hw

/-! ## 8. Clause (c): q-parameter cards under the exact coprimality hypothesis -/

/-- The exact Clause (c) coprimality input for the full bad moduli set
{3, 5, 7}: the fixed prime l is prime to 3, 5 and 7. -/
def S1729LTorsionCompatible (l : PrimeGeFive) : Prop :=
  Nat.Coprime 3 l.value ∧ Nat.Coprime 5 l.value ∧ Nat.Coprime 7 l.value

theorem S1729Two_coprime (l : PrimeGeFive) : Nat.Coprime 2 l.value :=
  (Nat.coprime_primes Nat.prime_two l.prime).mpr (by
    have := l.ge_five
    omega)

theorem S1729Three_coprime (l : PrimeGeFive) : Nat.Coprime 3 l.value :=
  (Nat.coprime_primes Nat.prime_three l.prime).mpr (by
    have := l.ge_five
    omega)

theorem S1729Six_coprime (l : PrimeGeFive) : Nat.Coprime 6 l.value := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.coprime_mul_iff_left]
  exact ⟨S1729Two_coprime l, S1729Three_coprime l⟩

theorem S1729Five_coprime_iff (l : PrimeGeFive) :
    Nat.Coprime 5 l.value ↔ l.value ≠ 5 := by
  rw [Nat.coprime_primes Nat.prime_five l.prime]
  constructor
  · intro h h5
    exact h h5.symm
  · intro h5 h
    exact h5 h.symm

theorem S1729Seven_coprime_iff (l : PrimeGeFive) :
    Nat.Coprime 7 l.value ↔ l.value ≠ 7 := by
  rw [Nat.coprime_primes Nat.prime_seven l.prime]
  constructor
  · intro h h7
    exact h h7.symm
  · intro h7 h
    exact h7 h.symm

/-- The hypothesis S1729LTorsionCompatible l holds as soon as l is not 5
and not 7 (which is automatic for l >= 11). -/
theorem S1729LTorsionCompatible_of_ne (l : PrimeGeFive)
    (h5 : l.value ≠ 5) (h7 : l.value ≠ 7) :
    S1729LTorsionCompatible l :=
  ⟨S1729Three_coprime l, (S1729Five_coprime_iff l).mpr h5,
    (S1729Seven_coprime_iff l).mpr h7⟩

/-- Exact form of the Clause (c) input for the full set {3, 5, 7}: it holds
exactly when l != 5 and l != 7. -/
theorem S1729LTorsionCompatible_iff (l : PrimeGeFive) :
    S1729LTorsionCompatible l ↔ (l.value ≠ 5 ∧ l.value ≠ 7) :=
  ⟨fun h => ⟨(S1729Five_coprime_iff l).mp h.2.1,
    (S1729Seven_coprime_iff l).mp h.2.2⟩,
    fun h => S1729LTorsionCompatible_of_ne l h.1 h.2⟩

/-- The type-I_n order attached to a place above a bad moduli place: 2 above 7
(type I_2), and 6 above 3 and 5 (type I_6).  These are the exponents of the
S1667 discriminant at 3, 5 and 7. -/
def S1729BadOrder (w : NumberField.FinitePlace S1720Field)
    (_hw : NumberFieldFinitePlace.comap (k := ℚ) w ∈ S1729VModBad) : ℕ :=
  if NumberFieldFinitePlace.residueCharacteristic
      (NumberFieldFinitePlace.comap (k := ℚ) w) = 7 then 2 else 6

theorem S1729BadOrder_pos (w : NumberField.FinitePlace S1720Field)
    (hw : NumberFieldFinitePlace.comap (k := ℚ) w ∈ S1729VModBad) :
    0 < S1729BadOrder w hw := by
  unfold S1729BadOrder
  split_ifs <;> norm_num

theorem S1729BadOrder_primeToL (l : PrimeGeFive)
    (w : NumberField.FinitePlace S1720Field)
    (hw : NumberFieldFinitePlace.comap (k := ℚ) w ∈ S1729VModBad) :
    Nat.Coprime (S1729BadOrder w hw) l.value := by
  unfold S1729BadOrder
  split_ifs
  · exact S1729Two_coprime l
  · exact S1729Six_coprime l

/-- The residue-characteristic half of Clause (c) for the full bad set
{3, 5, 7}: every bad moduli place is prime to l, under the exact coprimality
hypothesis. -/
theorem S1729BadResidueCharacteristic_coprime (l : PrimeGeFive)
    (hL : S1729LTorsionCompatible l) :
    forall p : NumberField.FinitePlace ℚ, p ∈ S1729VModBad →
      Nat.Coprime (NumberFieldFinitePlace.residueCharacteristic p) l.value := by
  intro p hp
  rcases (S1729VModBad_mem_iff p).mp hp with rfl | rfl | rfl
  · rw [concreteThreePlace_residueCharacteristic]
    exact hL.1
  · rw [S1712ConcreteFivePlace_residueCharacteristic]
    exact hL.2.1
  · rw [concreteSevenPlace_residueCharacteristic]
    exact hL.2.2

/-- Clause (c) q-parameter cards at all three bad places, under the exact
coprimality hypothesis.  The orders are the type-I_n exponents 2 and 6. -/
noncomputable def S1729QParameterCards (l : PrimeGeFive)
    (hL : S1729LTorsionCompatible l) :
    BadPlaceQParameterCards (S1729Selection l) where
  badResidueCharacteristic_primeToL := S1729BadResidueCharacteristic_coprime l hL
  sourceQParameterOrder := S1729BadOrder
  sourceQParameterOrder_pos := fun w hw => S1729BadOrder_pos w hw
  sourceQParameterOrder_primeToL := fun w hw => S1729BadOrder_primeToL l w hw

/-! ## 9. The D3 partition and the D4 reduction clause over the full bad set -/

/-- Definition 3.1(a)(b)(e): the actual source place partition over the full
bad moduli set {3, 5, 7}. -/
noncomputable def S1729PlacePartition (l : PrimeGeFive) :
    Theorem311Source.SourcePlacePartition
      (Selected (S1729Selection l)) (Bad (S1729Selection l)) :=
  toSourcePlacePartition (S1729Selection l)

/-- Definition 3.1(b)(c)-assembled reduction clause: the actual curve has
stable / multiplicative / split multiplicative reduction at every place above
3, 5 and 7, with the completed-DVR proxy q-parameter. -/
noncomputable def S1729SourceReductionClause (l : PrimeGeFive)
    (C : BadPlaceReductionCards (S1729Selection l)) :
    Theorem311Source.SourceReductionClause
      (Selected (S1729Selection l)) (Bad (S1729Selection l)) :=
  toSourceReductionClause (S1729Selection l) C

/-- The unconditional reduction clause over the full bad moduli set. -/
noncomputable def S1729FullReductionClause (l : PrimeGeFive) :
    Theorem311Source.SourceReductionClause
      (Selected (S1729Selection l)) (Bad (S1729Selection l)) :=
  S1729SourceReductionClause l (S1729BadPlaceReductionCards l)

theorem S1729FullReductionClause_split (l : PrimeGeFive)
    (b : Bad (S1729Selection l)) :
    (S1729FullReductionClause l).splitMultiplicativeReduction b :=
  (S1729FullReductionClause l).splitMultiplicativeReduction_proved b

theorem S1729FullReductionClause_qParameter_nonzero (l : PrimeGeFive)
    (b : Bad (S1729Selection l)) :
    (S1729FullReductionClause l).qParameter b ≠ 0 :=
  (S1729FullReductionClause l).qParameter_nonzero b

theorem S1729FullReductionClause_qParameter_contracting (l : PrimeGeFive)
    (b : Bad (S1729Selection l)) :
    ‖(S1729FullReductionClause l).qParameter b‖ < 1 :=
  (S1729FullReductionClause l).qParameter_contracting b

/-! ## 10. The exact boundary at l = 5 and l = 7 -/

/-- The concrete l = 5 label. -/
def S1729Five : PrimeGeFive where
  value := 5
  prime := Nat.prime_five
  ge_five := le_rfl

/-- The concrete l = 7 label. -/
def S1729Seven : PrimeGeFive where
  value := 7
  prime := Nat.prime_seven
  ge_five := by norm_num

@[simp] theorem S1729Five_value : S1729Five.value = 5 := rfl

@[simp] theorem S1729Seven_value : S1729Seven.value = 7 := rfl

/-- Clause (c) is refuted at l = 5 for the full bad set {3, 5, 7}: the card
would require Nat.Coprime 5 5.  So the paper's condition (c) forces the fixed
prime l to be different from every bad residue characteristic, and at l = 5
the literal full set must omit 5 (or no card exists). -/
theorem S1729_clauseC_refuted_at_five :
    ¬ Nonempty (BadPlaceQParameterCards (S1729Selection S1729Five)) := by
  rintro ⟨C⟩
  have hmem : concreteFivePlace ∈ (S1729Selection S1729Five).V_mod_bad := by
    rw [S1729Selection_V_mod_bad]
    exact S1729VModBad_five_mem
  have hcop := C.badResidueCharacteristic_primeToL concreteFivePlace hmem
  have hcop' : Nat.Coprime
      (NumberFieldFinitePlace.residueCharacteristic
        (concreteFivePlace : NumberField.FinitePlace ℚ)) (5 : Nat) := hcop
  rw [S1712ConcreteFivePlace_residueCharacteristic] at hcop'
  exact absurd hcop' (by decide)

/-- Clause (c) is refuted at l = 7 for the full bad set {3, 5, 7}. -/
theorem S1729_clauseC_refuted_at_seven :
    ¬ Nonempty (BadPlaceQParameterCards (S1729Selection S1729Seven)) := by
  rintro ⟨C⟩
  have hmem : concreteSevenPlace ∈ (S1729Selection S1729Seven).V_mod_bad := by
    rw [S1729Selection_V_mod_bad]
    exact S1729VModBad_seven_mem
  have hcop := C.badResidueCharacteristic_primeToL concreteSevenPlace hmem
  have hcop' : Nat.Coprime
      (NumberFieldFinitePlace.residueCharacteristic
        (concreteSevenPlace : NumberField.FinitePlace ℚ)) (7 : Nat) := hcop
  rw [concreteSevenPlace_residueCharacteristic] at hcop'
  exact absurd hcop' (by decide)

/-! ## 11. Axiom footprint -/

#print axioms S1729_splitMultiplicativeReductionAtThree
#print axioms S1729PlaceAboveThree_comap
#print axioms S1720PlaceAboveThree_comap
#print axioms S1729PlaceAboveThree_residueCharacteristic
#print axioms S1729SplitAtPlaceAboveThree
#print axioms S1729Delta_norm_three
#print axioms S1729ThreeQDataActual
#print axioms S1729VModBad_three_distinct
#print axioms S1729VModBad_odd
#print axioms S1729Selection
#print axioms S1729BadFintype
#print axioms S1729BadPlaceReductionCards
#print axioms S1729QParameterCards
#print axioms S1729FullReductionClause
#print axioms S1729_clauseC_refuted_at_five
#print axioms S1729_clauseC_refuted_at_seven

end LeanFormal.IUT.XiFPaper.S1729FullBadPlaceActual

end
