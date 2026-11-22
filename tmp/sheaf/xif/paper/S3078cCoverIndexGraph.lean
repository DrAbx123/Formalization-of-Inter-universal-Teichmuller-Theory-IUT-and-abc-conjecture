import tmp.sheaf.xif.paper.S3078bTopologicalCoverGraphConnected
import tmp.sheaf.xif.paper.S3078ConnectedIndexGraph
import Mathlib.AlgebraicGeometry.OpenImmersion
noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3050ConnectedSite
open LeanFormal.IUT.XiFPaper.S3078ConnectedIndexGraph
open LeanFormal.IUT.XiFPaper.S3078bTopologicalCoverGraphConnected
namespace LeanFormal.IUT.XiFPaper.S3078cCoverIndexGraph

variable {S : S3050ConnectedScheme} {T : Over S} (R : Sieve T)

/-- The underlying open image of a sieve arrow in T.left.obj. -/
def S3078cOpenSet (i : R.arrows.category) : Set (T.left.obj.left) :=
  Set.range (Over.Hom.left (Over.Hom.left i.obj.hom).hom)

/-- Openness of the image, when the arrow is an open immersion. -/
theorem S3078cOpenSet_isOpen (i : R.arrows.category)
    [AlgebraicGeometry.IsOpenImmersion (Over.Hom.left (Over.Hom.left i.obj.hom).hom)] :
    IsOpen (S3078cOpenSet R i) :=
  AlgebraicGeometry.IsOpenImmersion.isOpen_range _

/-- A sufficient condition: all sieve arrows are open immersions. -/
def S3078cAllArrowsOpen : Prop :=
  ∀ i : R.arrows.category,
    AlgebraicGeometry.IsOpenImmersion (Over.Hom.left (Over.Hom.left i.obj.hom).hom)

/-- Assuming the covering and openness, the topological graph is connected. -/
theorem S3078c_topological_graph_connected
    (hTconn : ConnectedSpace (T.left.obj.left))
    (hopen : S3078cAllArrowsOpen R)
    (hcov : (⋃ i : R.arrows.category, S3078cOpenSet R i) = Set.univ)
    (hne : ∀ i : R.arrows.category, (S3078cOpenSet R i).Nonempty) :
    ∀ i j : R.arrows.category,
      Relation.ReflTransGen
        (fun i j => (S3078cOpenSet R i ∩ S3078cOpenSet R j).Nonempty) i j := by
  haveI : ∀ i : R.arrows.category,
      AlgebraicGeometry.IsOpenImmersion (Over.Hom.left (Over.Hom.left i.obj.hom).hom) := hopen
  letI : PreconnectedSpace (T.left.obj.left) := inferInstance
  exact S3078TopologicalCoverGraphConnected (S3078cOpenSet R)
    (fun i => S3078cOpenSet_isOpen R i) hcov hne

#check S3078cOpenSet
#check S3078cOpenSet_isOpen
#check S3078cAllArrowsOpen
#check S3078c_topological_graph_connected
#print axioms S3078c_topological_graph_connected

end LeanFormal.IUT.XiFPaper.S3078cCoverIndexGraph