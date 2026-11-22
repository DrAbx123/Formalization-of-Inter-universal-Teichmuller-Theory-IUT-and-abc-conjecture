import tmp.sheaf.xif.paper.Mzk1Section0SaturatedActual
import tmp.sheaf.xif.paper.Mzk1Section0SaturatedSymmActual

/-!
# Mzk1Section0SaturatedClosureV2ActualAdapted (adapted copy, A475 reuse) — closure properties of saturated path-pair sets
(corpus Section 0, l.1337-1365)

STEP 0 prior-art: Mzk1Section0SaturatedActual (IsSaturatedPathPairSet conditions (a)-(e),
covertSet saturated), Mzk1Section0SaturatedSymmActual (symmetric saturation) -> REUSE.

This file proves that saturated path-pair sets are closed under arbitrary intersections and
containment in the all-co-verticial set, and that the empty set is saturated.

No axiom/sorry; registry frozen 14041.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0SaturatedClosureV2ActualAdapted

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual
open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual.OrientedGraph
open LeanFormal.IUT.XiFPaper.Mzk1Section0SaturatedActual
open LeanFormal.IUT.XiFPaper.Mzk1Section0SaturatedSymmActual

variable {G : OrientedGraph.{0}}

/-- The empty set of path pairs is saturated. -/
theorem saturated_empty (C : PathComposition G) :
    IsSaturatedPathPairSet C (∅ : Set (PathPairSigma G)) :=
  ⟨fun _ hp => absurd hp (by simp),
   fun _ hp => absurd hp (by simp),
   fun _ hp => absurd hp (by simp),
   fun _ _ _ h1 _ => absurd h1 (by simp),
   fun _ _ _ _ h1 _ _ => absurd h1 (by simp),
   fun _ _ _ _ h1 _ _ => absurd h1 (by simp)⟩

/-- Saturated path-pair sets are closed under intersections. -/
theorem saturated_inter (C : PathComposition G) (P Q : Set (PathPairSigma G))
    (hP : IsSaturatedPathPairSet C P) (hQ : IsSaturatedPathPairSet C Q) :
    IsSaturatedPathPairSet C (P ∩ Q) where
  diag_left p hp := ⟨hP.diag_left p hp.1, hQ.diag_left p hp.2⟩
  diag_right p hp := ⟨hP.diag_right p hp.1, hQ.diag_right p hp.2⟩
  covert p hp := hP.covert p hp.1
  trans γ1 γ2 γ3 h12 h23 :=
    ⟨hP.trans γ1 γ2 γ3 h12.1 h23.1, hQ.trans γ1 γ2 γ3 h12.2 h23.2⟩
  precomp γ1 γ2 γ3 hp h1 h2 :=
    ⟨hP.precomp γ1 γ2 γ3 hp.1 h1 h2, hQ.precomp γ1 γ2 γ3 hp.2 h1 h2⟩
  postcomp γ1 γ2 γ3 hp h1 h2 :=
    ⟨hP.postcomp γ1 γ2 γ3 hp.1 h1 h2, hQ.postcomp γ1 γ2 γ3 hp.2 h1 h2⟩

/-- Saturated path-pair sets are closed under arbitrary intersections. -/
theorem saturated_iInter (C : PathComposition G) {ι : Type*} [Nonempty ι]
    (Ps : ι → Set (PathPairSigma G))
    (h : ∀ i, IsSaturatedPathPairSet C (Ps i)) :
    IsSaturatedPathPairSet C (⋂ i, Ps i) where
  diag_left p hp := Set.mem_iInter.mpr fun i => (h i).diag_left p (Set.mem_iInter.mp hp i)
  diag_right p hp := Set.mem_iInter.mpr fun i => (h i).diag_right p (Set.mem_iInter.mp hp i)
  covert p hp :=
    (h (Classical.arbitrary ι)).covert p (Set.mem_iInter.mp hp (Classical.arbitrary ι))
  trans γ1 γ2 γ3 h12 h23 :=
    Set.mem_iInter.mpr fun i =>
      (h i).trans γ1 γ2 γ3 (Set.mem_iInter.mp h12 i) (Set.mem_iInter.mp h23 i)
  precomp γ1 γ2 γ3 hp h1 h2 :=
    Set.mem_iInter.mpr fun i => (h i).precomp γ1 γ2 γ3 (Set.mem_iInter.mp hp i) h1 h2
  postcomp γ1 γ2 γ3 hp h1 h2 :=
    Set.mem_iInter.mpr fun i => (h i).postcomp γ1 γ2 γ3 (Set.mem_iInter.mp hp i) h1 h2

/-- A saturated set is contained in the all-co-verticial set (restated for closure use). -/
theorem saturated_subset_covertSet (C : PathComposition G) (P : Set (PathPairSigma G))
    (h : IsSaturatedPathPairSet C P) : P ⊆ covertSet G :=
  saturated_subset_covert C P h

/-- Closure rows: (item, theorem, status). -/
def saturatedClosureRows : List (String × String × String) :=
  [ ("empty set is saturated", "saturated_empty", "PROVED"),
    ("intersection of saturated sets", "saturated_inter", "PROVED"),
    ("arbitrary intersection of saturated sets", "saturated_iInter", "PROVED"),
    ("saturated subset of covert", "saturated_subset_covertSet", "PROVED"),
    ("closure under gamma-equal pre/post composition (paper)", "not asserted beyond (d)/(e) fields", "NAMED") ]

/-- The closure row record has five rows. -/
theorem saturatedClosureRows_length : saturatedClosureRows.length = 5 := rfl

#check saturated_empty
#check saturated_inter
#check saturated_iInter
#check saturated_subset_covertSet
#check saturatedClosureRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Section0SaturatedClosureV2ActualAdapted
end
