import tmp.sheaf.xif.paper.S2568S2subsetAoc2Actual
import tmp.sheaf.xif.paper.S2567IsFractionRingAdjoinCActual
noncomputable section
set_option maxHeartbeats 16000000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2569S2subsetAoc2UncondActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2566AdjoinIntegralCActual
open LeanFormal.IUT.XiFPaper.S2567IsFractionRingAdjoinCActual
open LeanFormal.IUT.XiFPaper.S2568S2subsetAoc2Actual
theorem S2_le_Aoc2_uncond
    (h : IsIntegrallyClosed Aoc2) :
    ∀ s : S, algebraMap S L s ∈ Aoc2 := by
  haveI : IsFractionRing Aoc2 L := S2567_isFractionRing
  exact LeanFormal.IUT.XiFPaper.S2568S2subsetAoc2Actual.S2_le_Aoc2_of_integrallyClosed h
#print axioms S2_le_Aoc2_uncond
end LeanFormal.IUT.XiFPaper.S2569S2subsetAoc2UncondActual
end
