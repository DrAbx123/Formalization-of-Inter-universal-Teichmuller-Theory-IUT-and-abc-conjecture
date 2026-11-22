import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic

/-!
# S1713: split multiplicative reduction of the S1667 curve at five

The S1667 curve is the Legendre curve

  E : y^2 = x^3 + (61/64) x^2 - (125/64) x

over Q.  At the rational place 5 the model is already integral and its
discriminant has valuation six, while c_4 = 27721/256 is a 5-adic unit.
This file proves, with the actual completion and its valuation ring, that the
base-changed curve has split multiplicative reduction.  The witness is the
identity change of variables; the tangent quadratic is X^2 + 1 over F_5.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1713SplitReductionActual

open WeierstrassCurve
open Polynomial
open LeanFormal.IUT

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-! ## 0. The S1667 curve -/

/-- The Legendre curve y^2 = x^3 + (61/64) x^2 - (125/64) x. -/
def S1667Curve : WeierstrassCurve ℚ :=
  WeierstrassCurve.mk 0 (61 / 64) 0 (-125 / 64) 0

theorem S1667Curve_c₄ : S1667Curve.c₄ = (27721 / 256 : ℚ) := by
  norm_num [S1667Curve, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄]

theorem S1667Curve_Δ : S1667Curve.Δ = (558140625 / 1048576 : ℚ) := by
  norm_num [S1667Curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem S1667Curve_Δ_ne_zero : S1667Curve.Δ ≠ 0 := by
  rw [S1667Curve_Δ]
  norm_num

theorem S1667Curve_isElliptic : S1667Curve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr S1667Curve_Δ_ne_zero⟩

/-- The punctured S1667 curve, punctured at infinity. -/
def S1667Punctured : PuncturedEllipticCurve ℚ where
  curve := S1667Curve
  isElliptic := S1667Curve_isElliptic
  puncture := ⟨WeierstrassCurve.Projective.nonsingularLift_zero⟩

/-! ## 1. The integral model over Z_5 -/

abbrev K5 := ℚ_[5]

abbrev R5 := ℤ_[5]

/-- 61/64 is a 5-adic unit. -/
lemma norm_61_64 : ‖(61 / 64 : K5)‖ = 1 := by
  rw [show (61 / 64 : K5) = ((61 : ℕ) : K5) / ((64 : ℕ) : K5) by norm_num]
  rw [norm_div]
  have h1 : ‖((61 : ℕ) : K5)‖ = 1 :=
    (Padic.norm_natCast_eq_one_iff (p := 5) (n := 61)).2 (by norm_num)
  have h2 : ‖((64 : ℕ) : K5)‖ = 1 :=
    (Padic.norm_natCast_eq_one_iff (p := 5) (n := 64)).2 (by norm_num)
  rw [h1, h2]
  norm_num

/-- -125/64 lies in the maximal ideal of Z_5. -/
lemma norm_neg125_64_lt_one : ‖(-125 / 64 : K5)‖ < 1 := by
  rw [show (-125 / 64 : K5) = ((-125 : ℤ) : K5) / ((64 : ℕ) : K5) by norm_num]
  rw [norm_div]
  have h1 : ‖((-125 : ℤ) : K5)‖ < 1 := by
    rw [Padic.norm_intCast_lt_one_iff]
    norm_num
  have h2 : ‖((64 : ℕ) : K5)‖ = 1 :=
    (Padic.norm_natCast_eq_one_iff (p := 5) (n := 64)).2 (by norm_num)
  rw [h2, div_one]
  exact h1

/-- The lift of 61/64 to Z_5. -/
def z2 : R5 := ⟨(61 / 64 : K5), le_of_eq norm_61_64⟩

/-- The lift of -125/64 to Z_5. -/
def z4 : R5 := ⟨(-125 / 64 : K5), le_of_lt norm_neg125_64_lt_one⟩

/-- The explicit integral model of the S1667 curve at 5. -/
def I0 : WeierstrassCurve R5 :=
  WeierstrassCurve.mk 0 z2 0 z4 0

lemma z2_mul_64 : z2 * (64 : R5) = (61 : R5) := by
  apply Subtype.ext
  change (61 / 64 : K5) * (64 : K5) = (61 : K5)
  norm_num

lemma z4_mul_64 : z4 * (64 : R5) = (-125 : R5) := by
  apply Subtype.ext
  change (-125 / 64 : K5) * (64 : K5) = (-125 : K5)
  norm_num

/-- The integral model base-changes to the completion of the S1667 curve. -/
theorem I0_baseChange :
    I0.map (algebraMap R5 K5) = S1667Curve.baseChange K5 := by
  ext <;> simp [I0, z2, z4, S1667Curve, WeierstrassCurve.baseChange]

/-- The reduction of the integral model, over F_5. -/
def J : WeierstrassCurve (ZMod 5) :=
  I0.map (PadicInt.toZMod (p := 5))

lemma toZMod_64 : PadicInt.toZMod (64 : R5) = 4 := by
  rw [show (64 : R5) = ((64 : ℕ) : R5) by norm_num]
  rw [map_natCast]
  decide

lemma toZMod_61 : PadicInt.toZMod (61 : R5) = 1 := by
  rw [show (61 : R5) = ((61 : ℕ) : R5) by norm_num]
  rw [map_natCast]
  decide

lemma toZMod_neg125 : PadicInt.toZMod (-125 : R5) = 0 := by
  rw [show (-125 : R5) = ((-125 : ℤ) : R5) by norm_num]
  rw [map_intCast]
  decide

lemma toZMod_z2 : PadicInt.toZMod z2 = 4 := by
  have hz : PadicInt.toZMod z2 * (4 : ZMod 5) = 1 := by
    have h := congrArg (PadicInt.toZMod (p := 5)) z2_mul_64
    rw [map_mul, toZMod_64, toZMod_61] at h
    exact h
  have h4 : ((4 : ZMod 5) * 4) = 1 := by decide
  calc PadicInt.toZMod z2 = PadicInt.toZMod z2 * 1 := by ring
    _ = PadicInt.toZMod z2 * ((4 : ZMod 5) * 4) := by rw [h4]
    _ = (PadicInt.toZMod z2 * 4) * 4 := by ring
    _ = 1 * 4 := by rw [hz]
    _ = 4 := by norm_num

lemma toZMod_z4 : PadicInt.toZMod z4 = 0 := by
  have hz : PadicInt.toZMod z4 * (4 : ZMod 5) = 0 := by
    have h := congrArg (PadicInt.toZMod (p := 5)) z4_mul_64
    rw [map_mul, toZMod_64, toZMod_neg125] at h
    exact h
  have h4 : ((4 : ZMod 5) * 4) = 1 := by decide
  calc PadicInt.toZMod z4 = PadicInt.toZMod z4 * 1 := by ring
    _ = PadicInt.toZMod z4 * ((4 : ZMod 5) * 4) := by rw [h4]
    _ = (PadicInt.toZMod z4 * 4) * 4 := by ring
    _ = 0 * 4 := by rw [hz]
    _ = 0 := by norm_num

lemma J_eq : J = WeierstrassCurve.mk (0 : ZMod 5) 4 0 0 0 := by
  ext <;> simp [J, I0, toZMod_z2, toZMod_z4]

lemma J_c4 : J.c₄ = (1 : ZMod 5) := by
  rw [J_eq]
  decide

lemma J_delta : J.Δ = (0 : ZMod 5) := by
  rw [J_eq]
  decide

/-! ## 2. The split tangent polynomial X^2 + 1 -/

/-- The split tangent polynomial of the reduced model is X^2 + 1. -/
lemma J_splitReductionPolynomial :
    splitReductionPolynomial J = (X ^ 2 + 1 : (ZMod 5)[X]) := by
  rw [J_eq]
  simp [splitReductionPolynomial, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  rw [show (4 : ZMod 5) = -1 by decide]
  have hsq : (C (-1 : ZMod 5) : (ZMod 5)[X]) * C (-1) = 1 := by
    rw [← Polynomial.C_mul]
    have h : (-1 : ZMod 5) * (-1) = 1 := by decide
    rw [h]
    rfl
  have hneg : (C (-1 : ZMod 5) : (ZMod 5)[X]) = -1 := by
    rw [Polynomial.C_neg, Polynomial.C_1]
  rw [hsq, hneg]
  ring

/-- X^2 + 1 factors as (X - 2) (X + 2) over F_5. -/
lemma X_sq_plus_one_factor :
    (X ^ 2 + 1 : (ZMod 5)[X]) = (X - C 2) * (X + C 2) := by
  simp only [Polynomial.C_ofNat]
  ring_nf
  have h1 : (1 : ZMod 5) = -4 := by
    have h : (4 : ZMod 5) = -1 := by decide
    rw [show (-4 : ZMod 5) = -(4 : ZMod 5) by rfl, h]
    ring
  have hpoly : (1 : (ZMod 5)[X]) = -4 := by
    calc (1 : (ZMod 5)[X]) = C (1 : ZMod 5) := rfl
      _ = C (-4 : ZMod 5) := by rw [h1]
      _ = -4 := by rw [Polynomial.C_neg, Polynomial.C_ofNat]
  rw [hpoly]

lemma X_sq_plus_one_splits : (X ^ 2 + 1 : (ZMod 5)[X]).Splits := by
  rw [X_sq_plus_one_factor]
  exact (Polynomial.Splits.X_sub_C 2).mul (Polynomial.Splits.X_add_C 2)

/-! ## 3. The tangent polynomial splits over the residue field -/

lemma toZMod_I0_c4 : PadicInt.toZMod I0.c₄ = 1 := by
  rw [← WeierstrassCurve.map_c₄ (f := PadicInt.toZMod (p := 5)) (W := I0)]
  exact J_c4

lemma toZMod_I0_delta : PadicInt.toZMod I0.Δ = 0 := by
  rw [← WeierstrassCurve.map_Δ (f := PadicInt.toZMod (p := 5)) (W := I0)]
  exact J_delta

lemma I0_c4_notMem_maximalIdeal : I0.c₄ ∉ IsLocalRing.maximalIdeal R5 := by
  rw [← PadicInt.ker_toZMod (p := 5)]
  intro h
  have hzero : PadicInt.toZMod I0.c₄ = 0 := RingHom.mem_ker.mp h
  rw [toZMod_I0_c4] at hzero
  exact one_ne_zero hzero

lemma I0_delta_mem_maximalIdeal : I0.Δ ∈ IsLocalRing.maximalIdeal R5 := by
  rw [← PadicInt.ker_toZMod (p := 5)]
  exact RingHom.mem_ker.mpr toZMod_I0_delta

theorem W5_isIntegral :
    WeierstrassCurve.IsIntegral R5 (S1667Curve.baseChange K5) :=
  ⟨⟨I0, I0_baseChange.symm⟩⟩

attribute [local instance] W5_isIntegral

theorem I0_integralModel_eq :
    (S1667Curve.baseChange K5).integralModel R5 = I0 := by
  letI : WeierstrassCurve.IsIntegral R5 (S1667Curve.baseChange K5) := W5_isIntegral
  apply WeierstrassCurve.map_injective
    (FaithfulSMul.algebraMap_injective R5 K5)
  change ((S1667Curve.baseChange K5).integralModel R5).baseChange K5 =
    I0.baseChange K5
  rw [WeierstrassCurve.baseChange_integralModel_eq]
  exact I0_baseChange.symm

/-! ## 4. Minimality and multiplicative reduction over Q_5 -/

theorem W5_c4_valuation :
    (IsDiscreteValuationRing.maximalIdeal R5).valuation K5
      (S1667Curve.baseChange K5).c₄ = 1 := by
  letI : WeierstrassCurve.IsIntegral R5 (S1667Curve.baseChange K5) := W5_isIntegral
  rw [← WeierstrassCurve.integralModel_c₄_eq R5 (S1667Curve.baseChange K5)]
  rw [I0_integralModel_eq]
  exact ((IsDiscreteValuationRing.maximalIdeal R5).valuation_eq_one_iff_notMem
    (K := K5)).mpr I0_c4_notMem_maximalIdeal

theorem W5_delta_valuation_lt_one :
    (IsDiscreteValuationRing.maximalIdeal R5).valuation K5
      (S1667Curve.baseChange K5).Δ < 1 := by
  letI : WeierstrassCurve.IsIntegral R5 (S1667Curve.baseChange K5) := W5_isIntegral
  rw [← WeierstrassCurve.integralModel_Δ_eq R5 (S1667Curve.baseChange K5)]
  rw [I0_integralModel_eq]
  exact ((IsDiscreteValuationRing.maximalIdeal R5).valuation_lt_one_iff_mem
    (K := K5) I0.Δ).mpr I0_delta_mem_maximalIdeal

theorem W5_isMinimal :
    WeierstrassCurve.IsMinimal R5 (S1667Curve.baseChange K5) := by
  letI : WeierstrassCurve.IsIntegral R5 (S1667Curve.baseChange K5) := W5_isIntegral
  exact isMinimal_of_isIntegral_valuation_c₄_eq_one R5
    (S1667Curve.baseChange K5) W5_c4_valuation

theorem W5_hasMultiplicativeReduction :
    (S1667Curve.baseChange K5).HasMultiplicativeReduction R5 := by
  letI : WeierstrassCurve.IsIntegral R5 (S1667Curve.baseChange K5) := W5_isIntegral
  letI : WeierstrassCurve.IsMinimal R5 (S1667Curve.baseChange K5) := W5_isMinimal
  exact
    { badReduction := W5_delta_valuation_lt_one
      multiplicativeReduction := W5_c4_valuation }

theorem W5_hasSplitMultiplicativeReduction :
    (S1667Curve.baseChange K5).HasSplitMultiplicativeReduction R5 := by
  letI : WeierstrassCurve.IsIntegral R5 (S1667Curve.baseChange K5) := W5_isIntegral
  letI : WeierstrassCurve.IsMinimal R5 (S1667Curve.baseChange K5) := W5_isMinimal
  letI : (S1667Curve.baseChange K5).HasMultiplicativeReduction R5 :=
    W5_hasMultiplicativeReduction
  refine { splitMultiplicativeReduction := ?_ }
  rw [I0_integralModel_eq]
  change Polynomial.Splits
    ((splitReductionPolynomial I0).map
      (algebraMap R5 (IsLocalRing.ResidueField R5)))
  let P : (IsLocalRing.ResidueField R5)[X] :=
    (splitReductionPolynomial I0).map (IsLocalRing.residue R5)
  let rf : IsLocalRing.ResidueField R5 ≃+* ZMod 5 := PadicInt.residueField (p := 5)
  have hcomp : rf.toRingHom.comp (IsLocalRing.residue R5) =
      PadicInt.toZMod (p := 5) :=
    (PadicInt.toZMod_eq_residueField_comp_residue (p := 5)).symm
  have hP : P.map rf.toRingHom = (X ^ 2 + 1 : (ZMod 5)[X]) := by
    calc P.map rf.toRingHom
        = (splitReductionPolynomial I0).map
            (rf.toRingHom.comp (IsLocalRing.residue R5)) := by
          simp only [P, Polynomial.map_map]
      _ = (splitReductionPolynomial I0).map (PadicInt.toZMod (p := 5)) := by
          rw [hcomp]
      _ = splitReductionPolynomial J := by
          rw [J, splitReductionPolynomial_map]
      _ = (X ^ 2 + 1 : (ZMod 5)[X]) := J_splitReductionPolynomial
  have hsplit : (P.map rf.toRingHom).Splits := by
    rw [hP]
    exact X_sq_plus_one_splits
  exact Polynomial.Splits.of_splits_map rf.toRingHom hsplit
    (fun a _ => ⟨rf.symm a, by simp⟩)

/-! ## 5. The actual rational place five -/

/-- Split multiplicative reduction of the S1667 curve at the concrete
rational place 5, with the identity change of variables. -/
theorem S1713_splitMultiplicativeReductionAtFive :
    S1667Punctured.HasSplitMultiplicativeReductionAt concreteFivePlace := by
  have hW : HasSplitMultiplicativeReductionOnMinimalModel R5
      (S1667Curve.baseChange K5) :=
    ⟨1, by simpa using W5_hasSplitMultiplicativeReduction⟩
  have hcomm :
      concreteFivePadicEquiv.toRingEquiv.toRingHom.comp (algebraMap R5 K5) =
      (algebraMap concreteFiveCompletionIntegers concreteFiveCompletion).comp
        concreteFivePadicIntEquiv.toRingEquiv.toRingHom := by
    apply RingHom.ext
    intro x
    dsimp only [RingHom.comp_apply]
    change concreteFivePadicEquiv
        (algebraMap concreteLocalIntegers concreteLocalField x) =
      algebraMap concreteFiveCompletionIntegers concreteFiveCompletion
        (concreteFivePadicIntEquiv x)
    change concreteFivePadicEquiv
        (algebraMap concreteLocalIntegers concreteLocalField x) =
      (concreteFivePadicIntEquiv x : concreteFiveCompletion)
    rw [concreteFivePadicIntEquiv_coe]
    congr 1
  letI : IsLocalHom concreteFivePadicIntEquiv.toRingEquiv.toRingHom := by
    refine ⟨fun x hx => ?_⟩
    simpa using hx.map concreteFivePadicIntEquiv.toRingEquiv.symm.toMonoidHom
  have hmap := hasSplitMultiplicativeReductionOnMinimalModel_map_of_commutes
    (R := R5) (S := concreteFiveCompletionIntegers)
    (K := K5) (L := concreteFiveCompletion)
    concreteFivePadicIntEquiv.toRingEquiv.toRingHom
    concreteFivePadicEquiv.toRingEquiv.toRingHom
    hcomm (S1667Curve.baseChange K5) hW
  have hWmap :
      (S1667Curve.baseChange K5).map concreteFivePadicEquiv.toRingEquiv.toRingHom =
      S1667Curve.baseChange concreteFiveCompletion := by
    ext <;> simp [WeierstrassCurve.baseChange]
  rw [hWmap] at hmap
  unfold PuncturedEllipticCurve.HasSplitMultiplicativeReductionAt
  let F : ∀ z : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
      WeierstrassCurve (z.adicCompletion ℚ) :=
    fun z => S1667Curve.baseChange (z.adicCompletion ℚ)
  have htransport :=
    transport_splitMultiplicativeReduction_along_heightOne_eq F
      concreteFivePlace_underlyingPrime.symm
      (by
        change HasSplitMultiplicativeReductionOnMinimalModel
          concreteFiveCompletionIntegers
          (S1667Curve.baseChange concreteFiveCompletion)
        exact hmap)
  simpa [F, S1667Punctured] using htransport

#print axioms S1713_splitMultiplicativeReductionAtFive

end LeanFormal.IUT.XiFPaper.S1713SplitReductionActual
