import tmp.sheaf.n8.closure.NativeBadFintypeProof
import LeanFormal.IUT.Foundations.Geometry.LocalReduction
import Mathlib.Tactic

/-!
# Alternative proof: local good vs multiplicative reduction are disjoint

Task-536 attempts NativeLocalReductionDisjoint by the Weierstrass
discriminant/valuation route, rather than by transferring Mathlib same-model
disjointness.

Core observation. Both presentation-independent predicates are existentials
over variable changes:

  HasMultiplicativeReductionAt X p =
    exists C, (C * localCurve).HasMultiplicativeReduction R;
  HasGoodReductionAt X p =
    exists D, (D * localCurve).HasGoodReduction R.

If A = C • W is a minimal multiplicative model and B = D • W is a minimal
good model, then A and B are two minimal Weierstrass equations of the same
curve. The minimal discriminant valuation is independent of the chosen
minimal model. Both HasMultiplicativeReduction and HasGoodReduction force
IsMinimal, hence integrality; maximality of valuation_Δ_aux for each minimal
model gives the two inequalities, hence equality of valuation_Δ_aux. But
good reduction has valuation Δ = 1 while multiplicative reduction has
valuation Δ < 1, a contradiction.

The only auxiliary statement is the minimal-model valuation comparison
valuation_aux_le_of_minimal_smul; it is proved here from Mathlib
IsMinimal.val_Δ_maximal. No same-model transfer lemma is assumed.

No arbitrary equivalence, True, PUnit, axiom or sorry is used. This is
write-only; compilation is queued for the watchdog.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.N8Closure.NativeLocalReductionDisjointAlt

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeBadFintypeProof
open WeierstrassCurve

universe u

/-! ## 1. Minimal discriminant valuation comparison -/

/-- If B = E • A and A is a minimal Weierstrass equation, then the minimal
discriminant valuation of B is at most that of A, provided B is also minimal.
This is the valuation form of minimality; it does not require an explicit
integrality theorem for E. -/
theorem valuation_aux_le_of_minimal_smul
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (A B : WeierstrassCurve K) [IsMinimal R A] [IsMinimal R B]
    (E : VariableChange K) (hE : B = E • A) :
    valuation_Δ_aux R B <= valuation_Δ_aux R A := by
  have hmax := (inferInstance : IsMinimal R A).val_Δ_maximal
  by_contra hnot
  have hle : valuation_Δ_aux R A <= valuation_Δ_aux R B := le_of_not_ge hnot
  have hBint : IsIntegral R (E • A) := by
    rw [← hE]
    infer_instance
  have hle' : valuation_Δ_aux R A <= valuation_Δ_aux R (E • A) := by
    rw [← hE]
    exact hle
  have hge : valuation_Δ_aux R B <= valuation_Δ_aux R A := by
    have := hmax.2 hBint (by simpa using hle')
    simpa [hE] using this
  exact hnot hge

/-- The minimal discriminant valuation is independent of the chosen minimal
model, for two minimal models related by a variable change. -/
theorem valuation_aux_eq_of_minimal_smul
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (A B : WeierstrassCurve K) [IsMinimal R A] [IsMinimal R B]
    (E : VariableChange K) (hE : B = E • A) :
    valuation_Δ_aux R B = valuation_Δ_aux R A := by
  have hle : valuation_Δ_aux R B <= valuation_Δ_aux R A :=
    valuation_aux_le_of_minimal_smul A B E hE
  have hrev : A = E⁻¹ • B := by
    rw [hE, inv_smul_smul]
  have hge : valuation_Δ_aux R A <= valuation_Δ_aux R B :=
    valuation_aux_le_of_minimal_smul B A E⁻¹ hrev
  exact le_antisymm hle hge

/-! ## 2. Good and multiplicative models are disjoint on one curve -/

/-- At a local field, a minimal good-reduction equation and a minimal
multiplicative-reduction equation for the same Weierstrass curve cannot both
exist. The argument compares their discriminant valuations via minimality. -/
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
    rw [mul_smul, inv_smul_smul]
  have hval : valuation_Δ_aux R B = valuation_Δ_aux R A :=
    valuation_aux_eq_of_minimal_smul A B E hE
  have hBint : IsIntegral R B := inferInstance
  have hAint : IsIntegral R A := inferInstance
  have hBΔ : (IsDiscreteValuationRing.maximalIdeal R).valuation K B.Δ = 1 := hG.goodReduction
  have hAΔ : (IsDiscreteValuationRing.maximalIdeal R).valuation K A.Δ < 1 := hM.badReduction
  have hvalB : valuation_Δ_aux R B = (IsDiscreteValuationRing.maximalIdeal R).valuation K B.Δ :=
    valuation_Δ_aux_eq_of_isIntegral R B
  have hvalA : valuation_Δ_aux R A = (IsDiscreteValuationRing.maximalIdeal R).valuation K A.Δ :=
    valuation_Δ_aux_eq_of_isIntegral R A
  have hEqVal : (IsDiscreteValuationRing.maximalIdeal R).valuation K B.Δ =
      (IsDiscreteValuationRing.maximalIdeal R).valuation K A.Δ := by
    rw [← hvalB, ← hvalA]
    exact congrArg Subtype.val hval
  rw [hEqVal] at hBΔ
  exact (ne_of_lt hAΔ) hBΔ

/-! ## 3. Presentation-independent local disjointness -/

/-- The exact missing local theorem NativeLocalReductionDisjoint, now proved
from minimal discriminant valuation comparison. -/
theorem nativeLocalReductionDisjoint_alt :
    NativeLocalReductionDisjoint := by
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

end LeanFormal.IUT.N8Closure.NativeLocalReductionDisjointAlt
