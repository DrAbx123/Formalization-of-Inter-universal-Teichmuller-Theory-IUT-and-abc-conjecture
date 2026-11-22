import LeanFormal.IUT.Foundations.AlgebraicGeometry.ClosedBallProperSpaceVerification
import Mathlib.Topology.Algebra.Valued.LocallyCompact

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

/-!
# Instances for the compact valuation integer ring from properness

`ClosedBallProperSpaceVerification.ClosedBallInstanceResidual` is the
conjunction

  `CompleteSpace 𝒪[K] ∧ IsDiscreteValuationRing 𝒪[K] ∧ Finite 𝓀[K]`.

The repaired candidate already proves `ProperSpace K`.  This file extracts the
three conjuncts from that properness using the Mathlib equivalences

  `ProperSpace K ↔ CompactSpace 𝒪[K]`
  `CompactSpace 𝒪[K] ↔ CompleteSpace 𝒪[K] ∧ IsDiscreteValuationRing 𝒪[K] ∧ Finite 𝓀[K]`,

proves `ClosedBallInstanceResidual` unconditionally, and closes the residual
equivalence.  No instance is postulated: every conjunct is obtained from the
actual properness theorem.

Contents:
* `compactSpace_integer_of_properSpace`;
* `completeSpace_integer_of_properSpace`;
* `isDiscreteValuationRing_integer_of_properSpace`;
* `finite_residueField_of_properSpace`;
* `closedBallInstanceResidual_holds`;
* `properSpace_iff_closedBallInstanceResidual`;
* `compactSpace_valuedInteger`.

No fake instance, no card, no production edits.
-/

noncomputable section

namespace LeanFormal.IUT.ClosedBallInstanceFromProperSpace

open scoped WithZero Valued
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.ClosedBallCompactness
open LeanFormal.IUT.ClosedBallProperSpaceVerification

universe u

local instance gaussianClosedBallInstanceIrreducibleFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨LeanFormal.IUT.gaussianPolynomial_irreducible⟩

/-- The canonical completion. -/
abbrev completionField : Type :=
  LeanFormal.IUT.ClosedBallCompactness.completionField

/-- The valuation integer ring as `𝒪[K]`. -/
abbrev valuedInteger : Subring completionField :=
  LeanFormal.IUT.NormalizedLogNormComparison.valuedInteger

/-! ## Compactness of the integer ring -/

/-- Properness gives compactness of the actual valuation integer ring via the
Mathlib equivalence `ProperSpace K ↔ CompactSpace 𝒪[K]`. -/
theorem compactSpace_integer_of_properSpace
    (h : ProperSpace completionField) : CompactSpace (𝒪[completionField]) :=
by
  rw [← Valued.integer.properSpace_iff_compactSpace_integer]
  exact h

theorem compactSpace_integer : CompactSpace (𝒪[completionField]) :=
  compactSpace_integer_of_properSpace properSpaceCanonicalCompletion

/-! ## The three conjuncts -/

theorem completeSpace_integer_of_properSpace
    (h : ProperSpace completionField) : CompleteSpace (𝒪[completionField]) :=
  (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
    (compactSpace_integer_of_properSpace h)).1

theorem isDiscreteValuationRing_integer_of_properSpace
    (h : ProperSpace completionField) :
    IsDiscreteValuationRing (𝒪[completionField]) :=
  (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
    (compactSpace_integer_of_properSpace h)).2.1

theorem finite_residueField_of_properSpace
    (h : ProperSpace completionField) : Finite (𝓀[completionField]) :=
  (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
    (compactSpace_integer_of_properSpace h)).2.2

theorem completeSpace_integer : CompleteSpace (𝒪[completionField]) :=
  completeSpace_integer_of_properSpace properSpaceCanonicalCompletion

theorem isDiscreteValuationRing_integer :
    IsDiscreteValuationRing (𝒪[completionField]) :=
  isDiscreteValuationRing_integer_of_properSpace properSpaceCanonicalCompletion

theorem finite_residueField : Finite (𝓀[completionField]) :=
  finite_residueField_of_properSpace properSpaceCanonicalCompletion

/-! ## Closing the residual -/

/-- The exact residual predicate is now inhabited, from actual properness. -/
theorem closedBallInstanceResidual_holds :
    ClosedBallInstanceResidual :=
  ⟨completeSpace_integer, isDiscreteValuationRing_integer, finite_residueField⟩

theorem properSpace_iff_closedBallInstanceResidual :
    ProperSpace completionField ↔ ClosedBallInstanceResidual :=
  ⟨closedBallInstanceResidual_of_properSpace,
    properSpace_of_closedBallInstanceResidual⟩

theorem closedBallInstanceResidual_iff_properSpace :
    ClosedBallInstanceResidual ↔ ProperSpace completionField :=
  properSpace_iff_closedBallInstanceResidual.symm

/-! ## Closed-ball/compactness checks -/

theorem compactSpace_valuedInteger : CompactSpace valuedInteger :=
by
  change CompactSpace (𝒪[completionField])
  exact compactSpace_integer

theorem isCompact_closedBall (x : completionField) (r : ℝ) :
    IsCompact (Metric.closedBall x r) :=
  ProperSpace.isCompact_closedBall x r

theorem compactSpace_closedBall (x : completionField) (r : ℝ) :
    CompactSpace (Metric.closedBall x r) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall x r)

theorem isCompact_sphere (x : completionField) (r : ℝ) :
    IsCompact (Metric.sphere x r) :=
  ProperSpace.isCompact_sphere x r


/-! ## Converse compactness/properness bridge -/

theorem properSpace_of_compactSpace_integer
    (h : CompactSpace (𝒪[completionField])) : ProperSpace completionField :=
by
  rw [Valued.integer.properSpace_iff_compactSpace_integer]
  exact h

theorem properSpace_iff_compactSpace_integer :
    ProperSpace completionField ↔ CompactSpace (𝒪[completionField]) :=
  Valued.integer.properSpace_iff_compactSpace_integer

theorem compactSpace_integer_iff_properSpace :
    CompactSpace (𝒪[completionField]) ↔ ProperSpace completionField :=
  properSpace_iff_compactSpace_integer.symm

/-! ## Projections of the residual predicate -/

theorem ClosedBallInstanceResidual.completeSpace
    (h : ClosedBallInstanceResidual) : CompleteSpace (𝒪[completionField]) :=
  h.1

theorem ClosedBallInstanceResidual.isDiscreteValuationRing
    (h : ClosedBallInstanceResidual) : IsDiscreteValuationRing (𝒪[completionField]) :=
  h.2.1

theorem ClosedBallInstanceResidual.finite_residueField
    (h : ClosedBallInstanceResidual) : Finite (𝓀[completionField]) :=
  h.2.2

/-- Properness is both sufficient and necessary for the compact integer ring. -/
theorem properSpace_of_instanceResidual
    (h : ClosedBallInstanceResidual) : ProperSpace completionField :=
  properSpace_of_closedBallInstanceResidual h

/-! ## Additional compactness consumers -/

theorem compactSpace_units_from_instanceResidual
    (h : ClosedBallInstanceResidual) :
    CompactSpace (LeanFormal.IUT.LocalFieldIntegralUnits.Integers completionField)ˣ :=
by
  letI : ProperSpace completionField := properSpace_of_instanceResidual h
  exact LeanFormal.IUT.LocalFieldIntegralUnits.compactSpace_units
    (K := completionField)

theorem finite_principalUnitQuotient_from_instanceResidual
    (h : ClosedBallInstanceResidual) :
    Finite ((LeanFormal.IUT.LocalFieldIntegralUnits.Integers completionField)ˣ ⧸
      LeanFormal.IUT.LocalFieldIntegralUnits.principalUnits) :=
by
  letI : ProperSpace completionField := properSpace_of_instanceResidual h
  exact LeanFormal.IUT.LocalFieldIntegralUnits.finite_principalUnitQuotient
    (K := completionField)

end LeanFormal.IUT.ClosedBallInstanceFromProperSpace

end
