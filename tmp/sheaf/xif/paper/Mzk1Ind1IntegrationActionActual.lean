import tmp.sheaf.xif.paper.Mzk1Ind1ActualSourceUnitLayerActual
import tmp.sheaf.xif.paper.Mzk1Ind1IntegralUnitMapActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Ind1IntegrationActionActual
open LeanFormal.IUT LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.Mzk1Ind1ActualSourceUnitLayerActual
open LeanFormal.IUT.XiFPaper.Mzk1Ind1IntegralUnitMapActual

variable {K : Type} [NormedField K] [IsUltrametricDist K]

/-- An actual algebraic-closure unit automorphism that preserves the integral
units in both directions.  This is the source-level Ind1 action as it appears
on the actual unit group; no inhabitant is supplied. -/
structure IntegralUnitStableAlgebraicAction (K : Type) [NormedField K]
    [IsUltrametricDist K] where
  algAction : (AlgebraicClosure K)ˣ ≃* (AlgebraicClosure K)ˣ
  mapsIntegers : ∀ u : (Integers K)ˣ,
    ∃ v : (Integers K)ˣ,
      integersUnitsToAlgClosure (K := K) v =
        algAction (integersUnitsToAlgClosure (K := K) u)
  mapsIntegers_symm : ∀ u : (Integers K)ˣ,
    ∃ v : (Integers K)ˣ,
      integersUnitsToAlgClosure (K := K) v =
        algAction.symm (integersUnitsToAlgClosure (K := K) u)

def IntegralUnitStableAlgebraicActionRequired (K : Type) [NormedField K]
    [IsUltrametricDist K] : Prop :=
  Nonempty (IntegralUnitStableAlgebraicAction K)

theorem integralUnitStableAlgebraicActionRequired_iff (K : Type) [NormedField K]
    [IsUltrametricDist K] :
    IntegralUnitStableAlgebraicActionRequired K ↔
      Nonempty (IntegralUnitStableAlgebraicAction K) := Iff.rfl

#print axioms integralUnitStableAlgebraicActionRequired_iff
end LeanFormal.IUT.XiFPaper.Mzk1Ind1IntegrationActionActual