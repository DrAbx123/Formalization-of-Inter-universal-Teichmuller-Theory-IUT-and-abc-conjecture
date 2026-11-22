import LeanFormal.IUT.Foundations.AlgebraicGeometry.ClosedBallCompactness
import LeanFormal.IUT.Foundations.AlgebraicGeometry.CompletionProperSpaceConsumer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.DVRPrincipalRefinement
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import Mathlib.Topology.Algebra.Valued.LocallyCompact

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

/-!
# Verification of the repaired closed-ball / properness consumer

The repaired `ClosedBallCompactness` candidate proves

  `properSpaceCanonicalCompletion : ProperSpace completionField`.

This file checks the consumer chain: properness feeds the unconditional DVR
principal/torsion refinement (`CompletionProperSpaceConsumer`), the compact
integrals and quotient, and the closed-ball interfaces.  It also records the
exact remaining instance predicate for the compact valuation integer ring.

No fake instance, no card, no production edits.
-/

noncomputable section

namespace LeanFormal.IUT.ClosedBallProperSpaceVerification

open scoped WithZero Valued
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.UniformizerDVRDecomposition
open LeanFormal.IUT.ClosedBallCompactness
open LeanFormal.IUT.CompletionProperSpaceConsumer

universe u

local instance gaussianClosedBallVerificationIrreducibleFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨LeanFormal.IUT.gaussianPolynomial_irreducible⟩

/-- The canonical completion. -/
abbrev completionField : Type :=
  LeanFormal.IUT.ClosedBallCompactness.completionField

/-- The actual valuation integer ring. -/
abbrev valuedInteger : Subring completionField :=
  LeanFormal.IUT.NormalizedLogNormComparison.valuedInteger

/-! ## Properness and the candidate defeq -/

theorem completionField_defeq :
    LeanFormal.IUT.ClosedBallCompactness.completionField =
      LeanFormal.IUT.CompletionProperSpaceConsumer.completionField :=
  rfl

/-- Properness directly from the repaired candidate. -/
theorem properSpaceCanonicalCompletion : ProperSpace completionField :=
  LeanFormal.IUT.ClosedBallCompactness.properSpaceCanonicalCompletion

/-- The exact residual of the normalized consumer is now inhabited. -/
theorem completionProperSpaceResidual_holds :
    LeanFormal.IUT.NormalizedLogNormConsumer.CompletionProperSpaceResidual :=
  ⟨properSpaceCanonicalCompletion⟩

/-- Properness consumer form. -/
theorem properSpace_consumer : ProperSpace completionField :=
  properSpaceCanonicalCompletion

/-! ## Closed-ball and compactness interfaces -/

theorem isCompact_closedBall_of_properSpace (x : completionField) (r : ℝ) :
    IsCompact (Metric.closedBall x r) :=
  ProperSpace.isCompact_closedBall x r

theorem compactSpace_closedBall_of_properSpace (x : completionField) (r : ℝ) :
    CompactSpace (Metric.closedBall x r) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall_of_properSpace x r)

theorem isCompact_sphere_of_properSpace (x : completionField) (r : ℝ) :
    IsCompact (Metric.sphere x r) :=
  ProperSpace.isCompact_sphere x r

/-- The unit ball is the actual valuation integer ring. -/
theorem closedBall_zero_one_eq_valuedInteger :
    Metric.closedBall (0 : completionField) 1 = (valuedInteger : Set completionField) :=
  LeanFormal.IUT.ClosedBallCompactness.closedBall_zero_one_eq_valuedInteger

/-- The actual valuation integer ring is compact, from properness and the
unit-ball identification. -/
theorem compactSpace_valuedInteger : CompactSpace valuedInteger :=
by
  rw [← closedBall_zero_one_eq_valuedInteger]
  exact compactSpace_closedBall_of_properSpace 0 1

theorem compactSpace_integralUnits : CompactSpace
    (LeanFormal.IUT.LocalFieldIntegralUnits.Integers completionField)ˣ :=
  LeanFormal.IUT.CompletionProperSpaceConsumer.compactSpace_integralUnits_unconditional

theorem finite_principalUnitQuotient :
    Finite ((LeanFormal.IUT.LocalFieldIntegralUnits.Integers completionField)ˣ ⧸
      LeanFormal.IUT.LocalFieldIntegralUnits.principalUnits) :=
  LeanFormal.IUT.CompletionProperSpaceConsumer.finite_principalUnitQuotient_unconditional

/-! ## DVR principal/torsion refinement consumers -/

theorem exists_uniform_principalUnit_power_valued :
    ∃ N : ℕ, 0 < N ∧
      ∀ u : (valuedInteger)ˣ,
        u ^ N ∈ LeanFormal.IUT.NormalizedLogNormConsumer.valuedPrincipalUnits :=
  LeanFormal.IUT.CompletionProperSpaceConsumer.exists_uniform_principalUnit_power_valued_unconditional

theorem exists_uniformizer_dvr_principal_refinement
    (u : completionFieldˣ) :
    ∃ m : ℤ, ∃ u0 : (valuedInteger)ˣ,
      (u : completionField) = concreteAdicUniformizer ^ m *
        ((u0.val).1 : completionField) ∧
      ∃ N : ℕ, 0 < N ∧
        u0 ^ N ∈ LeanFormal.IUT.NormalizedLogNormConsumer.valuedPrincipalUnits :=
  LeanFormal.IUT.CompletionProperSpaceConsumer.exists_uniformizer_dvr_principal_refinement_unconditional u

theorem exists_uniformizer_dvr_valuation_refinement
    (u : completionFieldˣ) :
    ∃ m : ℤ, ∃ u0 : (valuedInteger)ˣ,
      (u : completionField) = concreteAdicUniformizer ^ m *
        ((u0.val).1 : completionField) ∧
      ∃ N : ℕ, 0 < N ∧
        (Valued.v ((((u0 ^ N).val).1 : completionField) - 1) :
          WithZero (Multiplicative ℤ)) < 1 :=
  LeanFormal.IUT.CompletionProperSpaceConsumer.exists_uniformizer_dvr_valuation_refinement_unconditional u

/-! ## Exact residual predicate for the compact integer ring -/

/-- The exact instance predicate needed by
`Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField`
for the canonical completion integer ring. -/
def ClosedBallInstanceResidual : Prop :=
  CompleteSpace (𝒪[completionField]) ∧
    IsDiscreteValuationRing (𝒪[completionField]) ∧
      Finite (𝓀[completionField])

/-- If the residual instance predicate holds, properness follows from the
Mathlib criterion, independently of the closed-ball scaling proof. -/
theorem properSpace_of_closedBallInstanceResidual
    (h : ClosedBallInstanceResidual) : ProperSpace completionField :=
by
  rw [Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField]
  exact h

/-- Conversely, properness gives the residual predicate through the same
criterion. -/
theorem closedBallInstanceResidual_of_properSpace
    (h : ProperSpace completionField) : ClosedBallInstanceResidual :=
by
  rw [← Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField]
  exact h

theorem properSpace_iff_closedBallInstanceResidual :
    ProperSpace completionField ↔ ClosedBallInstanceResidual :=
  ⟨closedBallInstanceResidual_of_properSpace,
    properSpace_of_closedBallInstanceResidual⟩


/-! ## Direct DVR refinement via the properness theorem -/

theorem exists_uniformizer_dvr_decomposition_with_principal_power
    (u : completionFieldˣ) :
    ∃ m : ℤ, ∃ u0 : (valuedInteger)ˣ,
      (u : completionField) = concreteAdicUniformizer ^ m *
        ((u0.val).1 : completionField) ∧
      ∃ N : ℕ, 0 < N ∧
        (Valued.v ((((u0 ^ N).val).1 : completionField) - 1) :
          WithZero (Multiplicative ℤ)) < 1 :=
by
  letI : ProperSpace completionField := properSpaceCanonicalCompletion
  exact LeanFormal.IUT.DVRPrincipalRefinement.exists_uniformizer_dvr_decomposition_with_principal_power u

theorem exists_uniformizer_dvr_norm_principal_power
    (u : completionFieldˣ) :
    ∃ m : ℤ, ∃ u0 : (valuedInteger)ˣ,
      (u : completionField) = concreteAdicUniformizer ^ m *
        ((u0.val).1 : completionField) ∧
      ∃ N : ℕ, 0 < N ∧
        ‖((((u0 ^ N).val).1 : completionField)) - 1‖ < 1 :=
by
  letI : ProperSpace completionField := properSpaceCanonicalCompletion
  exact LeanFormal.IUT.DVRPrincipalRefinement.exists_uniformizer_dvr_decomposition_with_norm_principal_power u

/-! ## Closed-ball / compactness interface checks -/

theorem isCompact_closedBall_zero_one :
    IsCompact (Metric.closedBall (0 : completionField) 1) :=
  isCompact_closedBall_of_properSpace 0 1

theorem isCompact_closedBall_zero (r : ℝ) :
    IsCompact (Metric.closedBall (0 : completionField) r) :=
  isCompact_closedBall_of_properSpace 0 r

theorem compactSpace_sphere (x : completionField) (r : ℝ) :
    CompactSpace (Metric.sphere x r) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere_of_properSpace x r)

theorem properSpace_consumer_closedBall (x : completionField) (r : ℝ) :
    IsCompact (Metric.closedBall x r) :=
  properSpace_consumer |> fun _ => isCompact_closedBall_of_properSpace x r

end LeanFormal.IUT.ClosedBallProperSpaceVerification

end
