import Mathlib.Topology.Connected.Basic
noncomputable section
open Set
namespace LeanFormal.IUT.XiFPaper.S3078bTopologicalCoverGraphConnected

/-- Connected space: the intersection graph of any open cover is connected. -/
theorem S3078TopologicalCoverGraphConnected
    {α : Type*} [TopologicalSpace α] [PreconnectedSpace α]
    {ι : Type*} (s : ι → Set α)
    (hopen : ∀ i, IsOpen (s i))
    (hcov : (⋃ i, s i) = univ)
    (hne : ∀ i, (s i).Nonempty) :
    ∀ i j : ι, Relation.ReflTransGen
      (fun i j => (s i ∩ s j).Nonempty) i j := by
  intro i j
  have hconn : IsPreconnected (⋃ i, s i) := by
    rw [hcov]
    exact isPreconnected_univ
  exact (hconn.transGen_of_iUnion hopen i j (hne i) (hne j)).to_reflTransGen

#check S3078TopologicalCoverGraphConnected
#print axioms S3078TopologicalCoverGraphConnected

end LeanFormal.IUT.XiFPaper.S3078bTopologicalCoverGraphConnected