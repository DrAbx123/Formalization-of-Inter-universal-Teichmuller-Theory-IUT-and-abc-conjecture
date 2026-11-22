import tmp.sheaf.xif.paper.S2559IsFractionRingAdjoinActual
noncomputable section
set_option maxHeartbeats 16000000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2560SsubsetAdjoinActual
open LeanFormal.IUT.XiFPaper.S2555ConcreteIntegralClosureActual
open LeanFormal.IUT.XiFPaper.S2556HZcMonicActual
open LeanFormal.IUT.XiFPaper.S2557AdjoinIntegralActual
open LeanFormal.IUT.XiFPaper.S2558ReverseReductionActual
open LeanFormal.IUT.XiFPaper.S2559IsFractionRingAdjoinActual
theorem S_le_adjoin_of_integrallyClosed
    (h : IsIntegrallyClosed Aoc) :
    ∀ s : S, algebraMap S L s ∈ Aoc := by
  haveI : IsFractionRing Aoc L := S2559_isFractionRing
  exact S2558ReverseReductionActual.S_le_adjoin_of_integrallyClosed h
#print axioms S_le_adjoin_of_integrallyClosed
end LeanFormal.IUT.XiFPaper.S2560SsubsetAdjoinActual
end
