import tmp.sheaf.xif.paper.S3077bOverBottomNotCovering
import tmp.sheaf.xif.paper.S3077ConnectedSheafExistence
noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3050ConnectedSite
open LeanFormal.IUT.XiFPaper.S3077bOverBottomNotCovering
namespace LeanFormal.IUT.XiFPaper.S3078ConnectedIndexGraph

/-- The index graph of a covering sieve: i and j are adjacent if they have a
common refinement in the over-site. -/
def S3078IndexGraphEdge {S : S3050ConnectedScheme} {T : Over S}
    (R : Sieve T) (i j : R.arrows.category) : Prop :=
  ∃ (Z : Over T) (g₁ : Z ⟶ i.obj) (g₂ : Z ⟶ j.obj), True

/-- The index graph is connected if every two indices are joined by a chain of
common refinements. -/
def S3078IndexGraphConnected {S : S3050ConnectedScheme} {T : Over S}
    (R : Sieve T) : Prop :=
  ∀ i j : R.arrows.category,
    Relation.ReflTransGen (S3078IndexGraphEdge R) i j

/-- Connected-site input: every covering sieve has a connected index graph. -/
def S3078CoverIndexGraphConnected : Prop :=
  ∀ (S : S3050ConnectedScheme) (T : Over S) (R : Sieve T),
    R ∈ S3050ConnectedSite.over S T → S3078IndexGraphConnected R

#check S3078IndexGraphEdge
#check S3078IndexGraphConnected
#check S3078CoverIndexGraphConnected

end LeanFormal.IUT.XiFPaper.S3078ConnectedIndexGraph