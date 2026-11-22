import tmp.sheaf.xif.paper.S2565ConcreteIntegralClosureCActual
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2566AdjoinIntegralCActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
local instance : Algebra S2562HZcMonicCActual.R2 L := inferInstanceAs (Algebra R L)
abbrev Aoc2 : Subalgebra R L := Algebra.adjoin R (HZc2.rootSet L)
theorem HZc2_root_isIntegral {x : L} (hx : x ∈ HZc2.rootSet L) : IsIntegral R x := by
  rw [mem_rootSet'] at hx
  exact ⟨HZc2, HZc2_monic, hx.2⟩
theorem adjoin2_le_integralClosure : Aoc2 ≤ integralClosure R L := by
  rw [Algebra.adjoin_le_iff]
  intro x hx
  exact HZc2_root_isIntegral hx
theorem adjoin2_root_integral {x : L} (hx : x ∈ Aoc2) : IsIntegral R x :=
  adjoin2_le_integralClosure hx
theorem adjoin2_subset_isIntegralClosure (x : L) (hx : x ∈ Aoc2) :
    ∃ s : S, algebraMap S L s = x := by
  haveI : IsIntegralClosure S R L := S2555_isIntegralClosure
  exact (IsIntegralClosure.isIntegral_iff (R := R) (A := S) (B := L)).mp
    (adjoin2_root_integral hx)
#print axioms adjoin2_subset_isIntegralClosure
end LeanFormal.IUT.XiFPaper.S2566AdjoinIntegralCActual
end
