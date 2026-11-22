import tmp.sheaf.xif.paper.Mzk1Ind1SourceUnitBridgeActual
import tmp.sheaf.xif.paper.Mzk1Ind1IntegralUnitMapActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Ind1ActualSourceUnitLayerActual
open LeanFormal.IUT LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.Mzk1Ind1SourceUnitBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1Ind1IntegralUnitMapActual

variable {K : Type} [NormedField K] [IsUltrametricDist K]
variable {L : Type} [NormedField L] [IsUltrametricDist L]
variable {p : Nat} [Fact p.Prime]
variable [CharZero K] [CompleteSpace K] [ProperSpace K]
variable [CharZero L] [CompleteSpace L] [ProperSpace L]
variable [NormedAlgebra ℚ_[p] K] [NormedAlgebra ℚ_[p] L]

/-- Actual source unit layer built directly from the integral units modulo
torsion.  This is the correction of the earlier algebraic-closure `F.Mon`
layer: it is finitely generated and matches `(Integers K)ˣ/tors` by
definition. -/
instance actualSourceUnitLayerTorsionNormal (K : Type) [NormedField K]
    [IsUltrametricDist K] :
    (CommGroup.torsion (Integers K)ˣ).Normal :=
  Subgroup.normal_of_comm _

abbrev ActualSourceUnitLayer (K : Type) [NormedField K]
    [IsUltrametricDist K] : Type :=
  (Integers K)ˣ ⧸ CommGroup.torsion (Integers K)ˣ

/-- The actual source unit layer identifies with the integral-unit torsion
quotient by definition. -/
def actualSourceUnitLayer_self (K : Type) [NormedField K]
    [IsUltrametricDist K] :
    SourceUnitQuotientIdentification (ActualSourceUnitLayer K) K where
  equiv := MulEquiv.refl _

theorem actualSourceUnitLayer_self_nonempty (K : Type) [NormedField K]
    [IsUltrametricDist K] :
    Nonempty (SourceUnitQuotientIdentification (ActualSourceUnitLayer K) K) :=
  ⟨actualSourceUnitLayer_self K⟩

/-- Given an actual source unit action on the integral-unit torsion quotient,
build the actual log-range isomorphism. -/
def actualSourceUnitLogRangeEquiv
    (β : ActualSourceUnitLayer K ≃* ActualSourceUnitLayer L) :
    (unitLogHom (K := K) (p := p)).range ≃*
      (unitLogHom (K := L) (p := p)).range :=
  sourceUnitLogRangeEquiv (p := p)
    (actualSourceUnitLayer_self K) (actualSourceUnitLayer_self L) β

#print axioms actualSourceUnitLayer_self_nonempty

/-- Actual Ind1 unit action at one local field: an actual algebraic-closure
unit automorphism together with its induced integral-unit quotient action.
The `compatible` field is the substantive provenance: the quotient action is
exactly the one induced by the actual algebraic-closure action on integral
units, not an arbitrary isomorphism. -/
structure ActualInd1UnitAction (K : Type) [NormedField K]
    [IsUltrametricDist K] where
  algAction : (AlgebraicClosure K)ˣ ≃* (AlgebraicClosure K)ˣ
  beta : ActualSourceUnitLayer K ≃* ActualSourceUnitLayer K
  compatible : ∀ u : (Integers K)ˣ, ∃ v : (Integers K)ˣ,
    beta (QuotientGroup.mk u) = QuotientGroup.mk v ∧
      integersUnitsToAlgClosure v =
        algAction (integersUnitsToAlgClosure u)

def ActualInd1UnitActionRequired (K : Type) [NormedField K]
    [IsUltrametricDist K] : Prop :=
  Nonempty (ActualInd1UnitAction K)

end LeanFormal.IUT.XiFPaper.Mzk1Ind1ActualSourceUnitLayerActual