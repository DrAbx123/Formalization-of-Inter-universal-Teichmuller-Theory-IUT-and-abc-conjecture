import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedLogNormConsumer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.ClosedBallCompactness
import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedLogNormComparison
import LeanFormal.IUT.Foundations.AlgebraicGeometry.UniformizerDVRDecomposition
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits

/-!
# Properness consumer for the normalized principal and DVR refinements

The closed-ball compactness candidate `ClosedBallCompactness.properSpaceCanonicalCompletion`
proves properness of the canonical Gaussian completion.  This file records the
definitional agreement of its `completionField` with the consumer completion,
proves the exact residual `NormalizedLogNormConsumer.CompletionProperSpaceResidual`,
and restates the normalized principal/DVR consumers without the conditional
properness premise.  No fake instance and no wrapper-only alias: every
unconditional theorem is a direct application of the candidate properness.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.CompletionProperSpaceConsumer

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.UniformizerDVRDecomposition
open scoped WithZero Valued

/-- The closed-ball compactness completion is definitionally the DVR consumer
completion. -/
theorem completionField_defeq :
    LeanFormal.IUT.ClosedBallCompactness.completionField =
      LeanFormal.IUT.UniformizerDVRDecomposition.completionField :=
  rfl

/-- Properness of the DVR consumer completion, transported from the closed-ball
compactness candidate. -/
theorem completionProperSpace : ProperSpace completionField := by
  rw [← completionField_defeq]
  exact LeanFormal.IUT.ClosedBallCompactness.properSpaceCanonicalCompletion

/-- The exact residual previously left in the normalized consumer is now
inhabited. -/
theorem completionProperSpaceResidual_holds :
    LeanFormal.IUT.NormalizedLogNormConsumer.CompletionProperSpaceResidual :=
  ⟨completionProperSpace⟩

/-- Properness consumer for the integral unit group compactness. -/
theorem completionProperSpace_consumer : ProperSpace completionField :=
  completionProperSpace

/-- Unconditional principal refinement: every actual integral unit has a
positive power in the actual principal-unit subgroup. -/
theorem exists_principalUnit_power_valued_integer_unit_unconditional
    (u : (Valued.v.integer : Subring completionField)ˣ) :
    ∃ N : Nat, 0 < N ∧
      u ^ N ∈ LeanFormal.IUT.NormalizedLogNormConsumer.valuedPrincipalUnits :=
  LeanFormal.IUT.NormalizedLogNormConsumer.exists_principalUnit_power_valued_integer_unit
    completionProperSpaceResidual_holds u

/-- Unconditional principal refinement in valuation-inequality form. -/
theorem exists_principalUnit_power_valuation_lt_one_unconditional
    (u : (Valued.v.integer : Subring completionField)ˣ) :
    ∃ N : Nat, 0 < N ∧
      (Valued.v ((((u ^ N).val).1 : completionField) - 1) :
        WithZero (Multiplicative Int)) < 1 :=
  LeanFormal.IUT.NormalizedLogNormConsumer.exists_principalUnit_power_valuation_lt_one
    completionProperSpaceResidual_holds u

/-- Unconditional uniform exponent theorem for all actual integral units. -/
theorem exists_uniform_principalUnit_power_valued_unconditional :
    ∃ N : Nat, 0 < N ∧
      ∀ u : (Valued.v.integer : Subring completionField)ˣ,
        u ^ N ∈ LeanFormal.IUT.NormalizedLogNormConsumer.valuedPrincipalUnits :=
  LeanFormal.IUT.NormalizedLogNormConsumer.exists_uniform_principalUnit_power_valued
    completionProperSpaceResidual_holds

/-- Unconditional DVR decomposition with principal refinement. -/
theorem exists_uniformizer_dvr_principal_refinement_unconditional
    (u : completionFieldˣ) :
    ∃ m : Int, ∃ u0 : (Valued.v.integer : Subring completionField)ˣ,
      (u : completionField) = concreteAdicUniformizer ^ m *
        ((u0.val).1 : completionField) ∧
      ∃ N : Nat, 0 < N ∧
        u0 ^ N ∈ LeanFormal.IUT.NormalizedLogNormConsumer.valuedPrincipalUnits :=
  LeanFormal.IUT.NormalizedLogNormConsumer.exists_uniformizer_dvr_principal_refinement
    completionProperSpaceResidual_holds u

/-- Unconditional DVR principal refinement in valuation-inequality form. -/
theorem exists_uniformizer_dvr_valuation_refinement_unconditional
    (u : completionFieldˣ) :
    ∃ m : Int, ∃ u0 : (Valued.v.integer : Subring completionField)ˣ,
      (u : completionField) = concreteAdicUniformizer ^ m *
        ((u0.val).1 : completionField) ∧
      ∃ N : Nat, 0 < N ∧
        (Valued.v ((((u0 ^ N).val).1 : completionField) - 1) :
          WithZero (Multiplicative Int)) < 1 :=
  LeanFormal.IUT.NormalizedLogNormConsumer.exists_uniformizer_dvr_valuation_refinement
    completionProperSpaceResidual_holds u

/-- Unconditional DVR decomposition with the integral part in the normalized
norm unit ball and with its principal power. -/
theorem exists_uniformizer_dvr_norm_unit_decomposition_unconditional
    (u : completionFieldˣ) :
    ∃ m : Int, ∃ u0 : (Integers completionField)ˣ,
      (u : completionField) = concreteAdicUniformizer ^ m *
        ((u0 : (Integers completionField)) : completionField) ∧
      ∃ N : Nat, 0 < N ∧ u0 ^ N ∈ principalUnits (K := completionField) :=
  LeanFormal.IUT.NormalizedLogNormConsumer.exists_uniformizer_dvr_norm_unit_decomposition
    completionProperSpaceResidual_holds u

/-- The unconditional principal refinement also gives the valuation inequality
for every power of a DVR integral unit. -/
theorem dvr_integralUnit_uniform_principal_power
    (u : (Valued.v.integer : Subring completionField)ˣ) :
    ∃ N : Nat, 0 < N ∧
      (Valued.v ((((u ^ N).val).1 : completionField) - 1) :
        WithZero (Multiplicative Int)) < 1 :=
  exists_principalUnit_power_valuation_lt_one_unconditional u

/-- The unconditional principal refinement is compatible with the chosen
uniform exponent; the exponent depends only on the completion, not on the unit. -/
theorem uniform_principal_power_of_all_units :
    ∃ N : Nat, 0 < N ∧
      ∀ u : (Valued.v.integer : Subring completionField)ˣ,
        (Valued.v ((((u ^ N).val).1 : completionField) - 1) :
          WithZero (Multiplicative Int)) < 1 :=
  by
  obtain ⟨N, hNpos, hN⟩ :=
    exists_uniform_principalUnit_power_valued_unconditional
  refine ⟨N, hNpos, ?_⟩
  intro u
  exact (LeanFormal.IUT.NormalizedLogNormConsumer.mem_valuedPrincipalUnits_iff _).mp (hN u)

/-- Properness is used only through the candidate theorem; this records the
exact defeq bridge and closes the residual. -/
theorem properSpace_residual_closed :
    LeanFormal.IUT.NormalizedLogNormConsumer.CompletionProperSpaceResidual ∧
      ProperSpace completionField :=
  ⟨completionProperSpaceResidual_holds, completionProperSpace⟩

/-- Unconditional compactness of the actual integral unit group. -/
theorem compactSpace_integralUnits_unconditional :
    CompactSpace (Integers completionField)ˣ :=
  LeanFormal.IUT.LocalFieldIntegralUnits.compactSpace_units
    (K := completionField)

/-- Unconditional finiteness of the normalized principal-unit quotient. -/
theorem finite_principalUnitQuotient_unconditional :
    Finite ((Integers completionField)ˣ ⧸
      principalUnits (K := completionField)) :=
  LeanFormal.IUT.LocalFieldIntegralUnits.finite_principalUnitQuotient
    (K := completionField)

/-- Unconditional uniform principal-unit exponent on the norm unit ball. -/
theorem exists_uniform_principalUnit_exponent_unconditional :
    ∃ N : Nat, 0 < N ∧
      ∀ u : (Integers completionField)ˣ,
        u ^ N ∈ principalUnits (K := completionField) :=
  LeanFormal.IUT.LocalFieldIntegralUnits.exists_uniform_principalUnit_exponent
    (K := completionField)

/-- The unconditional normalized exponent gives an explicit principal power for
the transported actual units. -/
theorem exists_transported_principal_power_unconditional
    (u : (CompletionIntegers concretePlace)ˣ) :
    ∃ N : Nat, 0 < N ∧
      (normalizedCompletionUnitsEquiv concretePlace).symm (u ^ N) ∈
        principalUnits (K := NormalizedCompletion concretePlace) := by
  obtain ⟨N, hNpos, hN⟩ :=
    exists_uniform_principalUnit_exponent_unconditional
  refine ⟨N, hNpos, ?_⟩
  rw [map_pow]
  exact hN ((normalizedCompletionUnitsEquiv concretePlace).symm u)

/-- Properness also gives compactness of the normalized integral unit group. -/
theorem compactSpace_normalizedIntegralUnits :
    CompactSpace (Integers (NormalizedCompletion concretePlace))ˣ :=
  LeanFormal.IUT.LocalFieldIntegralUnits.compactSpace_units
    (K := NormalizedCompletion concretePlace)

/-- The normalized principal quotient is finite under the transported
properness. -/
theorem finite_normalizedPrincipalQuotient_unconditional :
    Finite ((Integers (NormalizedCompletion concretePlace))ˣ ⧸
      principalUnits (K := NormalizedCompletion concretePlace)) :=
  LeanFormal.IUT.LocalFieldIntegralUnits.finite_principalUnitQuotient
    (K := NormalizedCompletion concretePlace)

/-- The candidate properness integrates with the DVR decomposition through the
exact same completion type. -/
theorem dvr_completionField_type_eq_candidate :
    LeanFormal.IUT.UniformizerDVRDecomposition.completionField =
      LeanFormal.IUT.ClosedBallCompactness.completionField :=
  rfl

/-- The properness residual and the unconditional principal refinement are
jointly available at the concrete source completion. -/
theorem completionProperSpace_residual_and_principal_refinement :
    LeanFormal.IUT.NormalizedLogNormConsumer.CompletionProperSpaceResidual ∧
      (∃ N : Nat, 0 < N ∧
        ∀ u : (Valued.v.integer : Subring completionField)ˣ,
          u ^ N ∈ LeanFormal.IUT.NormalizedLogNormConsumer.valuedPrincipalUnits) :=
  ⟨completionProperSpaceResidual_holds,
    exists_uniform_principalUnit_power_valued_unconditional⟩
end LeanFormal.IUT.CompletionProperSpaceConsumer
