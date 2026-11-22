import tmp.sheaf.xif.paper.AbsTopIII05Section0ObjectsActual

/-!
  Mainline: Section-0 saturated path-pair set laws (real proofs on the constructed
  abstract objects; extends AbsTopIII05Section0ObjectsActual).  Saturation is the
  invariance P = P under every edge-type-preserving vertex map; the lattice of
  saturated sets is therefore closed under complement/union/intersection.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0SaturationLawsActual

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual

universe u

theorem isSaturated_empty (G : OrientedGraph) (n : Nat) :
    OrientedGraph.IsSaturatedPathPairSet G n (∅ : Set (OrientedGraph.PathPair G n)) := by
  intro sigma hsigma
  rfl

theorem isSaturated_univ (G : OrientedGraph) (n : Nat) :
    OrientedGraph.IsSaturatedPathPairSet G n (Set.univ : Set (OrientedGraph.PathPair G n)) := by
  intro sigma hsigma
  rfl

theorem isSaturated_compl {G : OrientedGraph} {n : Nat}
    {P : Set (OrientedGraph.PathPair G n)}
    (h : OrientedGraph.IsSaturatedPathPairSet G n P) :
    OrientedGraph.IsSaturatedPathPairSet G n (Pᶜ) := by
  intro sigma hsigma
  rw [h sigma hsigma]

theorem isSaturated_inter {G : OrientedGraph} {n : Nat}
    {P Q : Set (OrientedGraph.PathPair G n)}
    (hp : OrientedGraph.IsSaturatedPathPairSet G n P)
    (hq : OrientedGraph.IsSaturatedPathPairSet G n Q) :
    OrientedGraph.IsSaturatedPathPairSet G n (P ∩ Q) := by
  intro sigma hsigma
  rw [hp sigma hsigma, hq sigma hsigma]

theorem isSaturated_union {G : OrientedGraph} {n : Nat}
    {P Q : Set (OrientedGraph.PathPair G n)}
    (hp : OrientedGraph.IsSaturatedPathPairSet G n P)
    (hq : OrientedGraph.IsSaturatedPathPairSet G n Q) :
    OrientedGraph.IsSaturatedPathPairSet G n (P ∪ Q) := by
  intro sigma hsigma
  rw [hp sigma hsigma, hq sigma hsigma]

end LeanFormal.IUT.XiFPaper.Mzk1Section0SaturationLawsActual