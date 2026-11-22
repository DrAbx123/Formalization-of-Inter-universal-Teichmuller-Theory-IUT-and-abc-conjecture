import tmp.sheaf.xif.paper.S2557AdjoinIntegralActual
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2558ReverseReductionActual
open LeanFormal.IUT.XiFPaper.S2555ConcreteIntegralClosureActual
open LeanFormal.IUT.XiFPaper.S2556HZcMonicActual
open LeanFormal.IUT.XiFPaper.S2557AdjoinIntegralActual
theorem S_le_adjoin_of_integrallyClosed
    [IsFractionRing Aoc L] (h : IsIntegrallyClosed Aoc) :
    ∀ s : S, algebraMap S L s ∈ Aoc := by
  intro s
  haveI : IsIntegralClosure S R L := S2555_isIntegralClosure
  have hxR : IsIntegral R (algebraMap S L s) :=
    IsIntegral.map (IsScalarTower.toAlgHom R S L)
      (IsIntegralClosure.isIntegral (R := R) (A := S) (B := L) s)
  have hxA : IsIntegral Aoc (algebraMap S L s) := hxR.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Aoc) (K := L)).mp hxA
  rw [← hy]
  exact y.2
#print axioms S_le_adjoin_of_integrallyClosed
end LeanFormal.IUT.XiFPaper.S2558ReverseReductionActual
end
