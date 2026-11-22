import tmp.sheaf.n8.closure.NativeBadFintypeProof
import LeanFormal.IUT.Foundations.Geometry.LocalReduction
import LeanFormal.IUT.ABCBridge.Geometry.FreyTwoAdicMinimalDiscriminantValuation

/-!
# Local good and multiplicative reduction are disjoint

Goal: prove NativeLocalReductionDisjoint, i.e.

  forall F [Field F] [NumberField F] (X : PuncturedEllipticCurve F)
    (p : NumberField.FinitePlace F),
      X.HasMultiplicativeReductionAt p -> not (X.HasGoodReductionAt p).

The proof uses the minimal-discriminant-valuation comparison for minimal
Weierstrass models.  If C and D are variable changes such that C • W has
multiplicative reduction and D • W has good reduction, then the two equations
are minimal models of the same curve.  Their minimal discriminant valuations
agree (valuation_Δ_aux_eq_of_isMinimal in
FreyTwoAdicMinimalDiscriminantValuation.lean).  But good reduction forces
valuation of Δ equal to 1, while multiplicative reduction forces it below 1,
a contradiction.

No same-model transfer is assumed; Mathlib's direct
HasMultiplicativeReduction.not_hasGoodReduction is not needed.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.N8Closure.NativeLocalReductionDisjoint

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeBadFintypeProof
open WeierstrassCurve
open IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

universe u

/-! ## 1. Two minimal reduction models of one curve are disjoint -/

theorem not_good_and_multiplicative_of_smul
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K)
    (C D : VariableChange K)
    (hM : (C • W).HasMultiplicativeReduction R)
    (hG : (D • W).HasGoodReduction R) : False := by
  let A : WeierstrassCurve K := C • W
  let B : WeierstrassCurve K := D • W
  haveI : IsMinimal R A := hM.toIsMinimal
  haveI : IsMinimal R B := hG.toIsMinimal
  let E : VariableChange K := D * C⁻¹
  have hE : B = E • A := by
    dsimp [A, B, E]
    rw [mul_smul]
    congr 1
    group
  have hval : valuation_Δ_aux R B = valuation_Δ_aux R A := by
    have hEA : E • A = B := hE.symm
    haveI : IsMinimal R (E • A) := by
      rw [hEA]
      infer_instance
    have h := valuation_Δ_aux_eq_of_isMinimal (R := R) (K := K) (W := A) E
    simpa [hEA] using h
  have hAint : IsIntegral R A := inferInstance
  have hBint : IsIntegral R B := inferInstance
  have hvalA : valuation_Δ_aux R A =
      valuation K (maximalIdeal R) A.Δ :=
    valuation_Δ_aux_eq_of_isIntegral R A
  have hvalB : valuation_Δ_aux R B =
      valuation K (maximalIdeal R) B.Δ :=
    valuation_Δ_aux_eq_of_isIntegral R B
  have hEqVal : valuation K (maximalIdeal R) B.Δ =
      valuation K (maximalIdeal R) A.Δ := by
    rw [← hvalB, ← hvalA]
    exact hval
  have hBΔ : valuation K (maximalIdeal R) B.Δ = 1 := hG.goodReduction
  have hAΔ : valuation K (maximalIdeal R) A.Δ < 1 := hM.badReduction
  rw [hEqVal] at hBΔ
  rw [hBΔ] at hAΔ
  exact lt_irrefl _ hAΔ

/-! ## 2. Presentation-independent local disjointness -/

theorem nativeLocalReductionDisjoint_actual :
    NativeLocalReductionDisjoint.{u} := by
  intro F _ _ X p hM hG
  let prime := NumberFieldFinitePlace.underlyingPrime p
  let K := prime.adicCompletion F
  let R := prime.adicCompletionIntegers F
  let W : WeierstrassCurve K := X.curve.baseChange K
  dsimp [PuncturedEllipticCurve.HasMultiplicativeReductionAt,
    PuncturedEllipticCurve.HasGoodReductionAt,
    HasMultiplicativeReductionOnMinimalModel,
    HasGoodReductionOnMinimalModel] at hM hG
  rcases hM with ⟨C, hC⟩
  rcases hG with ⟨D, hD⟩
  exact not_good_and_multiplicative_of_smul (R := R) (K := K) W C D hC hD

/-- The paper-facing exact target. -/
theorem nativeLocalReductionDisjoint :
    NativeLocalReductionDisjoint.{u} :=
  nativeLocalReductionDisjoint_actual

end LeanFormal.IUT.N8Closure.NativeLocalReductionDisjoint

end