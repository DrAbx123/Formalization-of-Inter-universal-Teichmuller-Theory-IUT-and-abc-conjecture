import tmp.sheaf.xif.paper.S2589TargetAssemblyActual
import tmp.sheaf.xif.paper.S2588FbarIrreducibleActual
import tmp.sheaf.xif.paper.S2584PrimeDegreeOneActual
import tmp.sheaf.xif.paper.S2592GenericLocalizedResidueIsoActual
import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
import tmp.sheaf.xif.paper.S2591LocalizedResidueEquivActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2593ConditionalChainActual

open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2587LocalizedResidueDataActual
open LeanFormal.IUT.XiFPaper.S2589TargetAssemblyActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual

abbrev OL : Type := NumberField.RingOfIntegers S2057FiveDivisionField

/-- Maximal prime of O_L over the base contraction q, from integrality. -/
theorem S2593_P0_exists
    (D : S2587LocalizedResidueDataS)
    (h613 : (algebraMap ℤ S) (613 : ℤ) ∈ D.p) :
    ∃ P0 : Ideal OL, P0.IsMaximal ∧
      P0.LiesOver (D.p.comap (algebraMap C S)) := by
  have hq : (D.p.comap (algebraMap C S)).IsMaximal :=
    LeanFormal.IUT.XiFPaper.S2590LocalizedPrimeContractionActual.S2590_contraction_maximal D h613
  exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (P := D.p.comap (algebraMap C S))

/-- The unique remaining input for the 12-cycle target. -/
def S2593UniqueRemaining : Prop :=
  S2587LocalizedDedekindToTwelveCycleS

/-- Conditional chain: the unique remaining input implies S2470Target. -/
theorem S2593Target_of_unique_remaining
    (h : S2593UniqueRemaining) :
    LeanFormal.IUT.XiFPaper.S2470PairTransitiveFinalActual.S2470Target := by
  obtain ⟨W⟩ := S2584_witness_nonempty
  exact S2587Target_of_witness_irreducible W
    (LeanFormal.IUT.XiFPaper.S2588FbarIrreducibleActual.S2587FbarIrreducibleRequired_holds W) h

end LeanFormal.IUT.XiFPaper.S2593ConditionalChainActual
end