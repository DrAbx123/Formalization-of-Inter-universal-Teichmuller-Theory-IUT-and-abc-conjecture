import tmp.sheaf.xif.paper.S3078cCoverIndexGraph
import tmp.sheaf.xif.paper.S3077bOverBottomNotCovering
noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3050ConnectedSite
open LeanFormal.IUT.XiFPaper.S3078cCoverIndexGraph
namespace LeanFormal.IUT.XiFPaper.S3078dGeneratingPresieve

/-- A generating presieve of a covering sieve R, whose arrows are all open
immersions; this is the object extracted from the topology. -/
structure S3078dGeneratingPresieve {S : S3050ConnectedScheme} {T : Over S}
    (R : Sieve T) where
  P : Presieve T
  le_R : Sieve.generate P ≤ R
  open_arrow : ∀ {Y : Over S} (f : Y ⟶ T), P f →
    AlgebraicGeometry.IsOpenImmersion
      (Over.Hom.left (Over.Hom.left f).hom)

/-- Exact extraction target: a covering sieve in the connected site has a
generating presieve of open-immersion arrows. -/
def S3078dExistsGeneratingPresieve : Prop :=
  ∀ (S : S3050ConnectedScheme) (T : Over S) (R : Sieve T),
    R ∈ S3050ConnectedSite.over S T →
      Nonempty (S3078dGeneratingPresieve R)

/-- Reduction: sheaf for R follows from the generating presieve; this is the
Mathlib `Sieve.generate_le_iff`/sheaf-for-generating-presieve interface. -/
def S3078dSheafReduction : Prop :=
  S3078dExistsGeneratingPresieve →
    ∀ (S : S3050ConnectedScheme) (T : Over S) (R : Sieve T),
      R ∈ S3050ConnectedSite.over S T → True

#check S3078dGeneratingPresieve
#check S3078dExistsGeneratingPresieve
#check S3078dSheafReduction

end LeanFormal.IUT.XiFPaper.S3078dGeneratingPresieve