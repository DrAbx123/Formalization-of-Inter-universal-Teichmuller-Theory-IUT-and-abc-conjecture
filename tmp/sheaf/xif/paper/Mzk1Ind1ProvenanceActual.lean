import tmp.sheaf.xif.paper.Mzk1Ind1ActualSourceUnitLayerActual
import tmp.sheaf.xif.paper.Mzk1Ind1IntegrationActionActual
import tmp.sheaf.xif.paper.Mzk1Ind1IntegralUnitMapActual
import LeanFormal.IUT.IUTII.Kummer.TimesMuQuotient
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Ind1ProvenanceActual
open LeanFormal.IUT LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.Mzk1Ind1ActualSourceUnitLayerActual
open LeanFormal.IUT.XiFPaper.Mzk1Ind1IntegralUnitMapActual

variable {K : Type} [NormedField K] [IsUltrametricDist K]

/-- Natural map from integral units to the algebraic-closure unit torsion
quotient. -/
def integersUnitsToTimesMu : (Integers K)ˣ →* TimesMuQuotient (AlgebraicClosure K)ˣ :=
  TimesMuQuotient.quotientMap.comp (integersUnitsToAlgClosure (K := K))

/-- The natural map kills torsion, so it descends to the actual source unit
layer `(Integers K)ˣ/tors`. -/
def actualSourceUnitToTimesMu :
    ActualSourceUnitLayer K →* TimesMuQuotient (AlgebraicClosure K)ˣ :=
  QuotientGroup.lift (CommGroup.torsion (Integers K)ˣ)
    (integersUnitsToTimesMu (K := K)) (by
      intro u hu
      rw [MonoidHom.mem_ker, TimesMuQuotient.quotientMap_ker]
      exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩)

/-- Substantive provenance for an actual Ind1 unit action: the integral-unit
quotient action `beta` is intertwined with an actual TimesMu action on the
algebraic-closure unit quotient, and the chosen `algAction` realizes this
TimesMu action on quotient classes.  This is an equality/square condition, not
a bare `Prop` field. -/
structure ActualInd1UnitActionProvenance (K : Type) [NormedField K]
    [IsUltrametricDist K] where
  algAction : (AlgebraicClosure K)ˣ ≃* (AlgebraicClosure K)ˣ
  beta : ActualSourceUnitLayer K ≃* ActualSourceUnitLayer K
  timesMuAction : TimesMuQuotient (AlgebraicClosure K)ˣ ≃*
    TimesMuQuotient (AlgebraicClosure K)ˣ
  algAction_timesMu : ∀ y : (AlgebraicClosure K)ˣ,
    timesMuAction (TimesMuQuotient.quotientMap y) =
      TimesMuQuotient.quotientMap (algAction y)
  square : ∀ x : ActualSourceUnitLayer K,
    actualSourceUnitToTimesMu (beta x) =
      timesMuAction (actualSourceUnitToTimesMu x)

def ActualInd1UnitActionProvenanceRequired (K : Type) [NormedField K]
    [IsUltrametricDist K] : Prop :=
  Nonempty (ActualInd1UnitActionProvenance K)

#print axioms actualSourceUnitToTimesMu
end LeanFormal.IUT.XiFPaper.Mzk1Ind1ProvenanceActual