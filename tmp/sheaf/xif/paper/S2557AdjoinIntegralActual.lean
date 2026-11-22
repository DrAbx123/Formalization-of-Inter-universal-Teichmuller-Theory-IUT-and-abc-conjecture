import tmp.sheaf.xif.paper.S2556HZcMonicActual
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2557AdjoinIntegralActual
open LeanFormal.IUT.XiFPaper.S2555ConcreteIntegralClosureActual
open LeanFormal.IUT.XiFPaper.S2556HZcMonicActual
abbrev Aoc : Subalgebra R L := Algebra.adjoin R (HZc.rootSet L)
theorem HZc_root_isIntegral {x : L} (hx : x ∈ HZc.rootSet L) : IsIntegral R x := by
  rw [mem_rootSet'] at hx
  exact ⟨HZc, HZc_monic, hx.2⟩
theorem adjoin_le_integralClosure : Aoc ≤ integralClosure R L := by
  rw [Algebra.adjoin_le_iff]
  intro x hx
  exact HZc_root_isIntegral hx
theorem adjoin_root_integral {x : L} (hx : x ∈ Aoc) : IsIntegral R x :=
  adjoin_le_integralClosure hx
theorem adjoin_subset_isIntegralClosure (x : L) (hx : x ∈ Aoc) :
    ∃ s : S, algebraMap S L s = x := by
  haveI : IsIntegralClosure S R L := S2555_isIntegralClosure
  exact (IsIntegralClosure.isIntegral_iff (R := R) (A := S) (B := L)).mp
    (adjoin_root_integral hx)
#print axioms adjoin_subset_isIntegralClosure
end LeanFormal.IUT.XiFPaper.S2557AdjoinIntegralActual
end
