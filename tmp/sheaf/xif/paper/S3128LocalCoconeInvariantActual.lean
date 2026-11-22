import tmp.sheaf.xif.paper.S3128SpecAutNaturalActual
import tmp.sheaf.xif.paper.S3128LocalCoconeActual

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LeanFormal.IUT.XiFPaper.S3128LocalCoconeInvariantActual

open LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual
open LeanFormal.IUT.XiFPaper.S3128SpecActionActual
open LeanFormal.IUT.XiFPaper.S3128AwayActionActual
open LeanFormal.IUT.XiFPaper.S3128AwayActionHomAttempt
open LeanFormal.IUT.XiFPaper.S3128SpecAutNaturalActual
open LeanFormal.IUT.XiFPaper.S3128LocalCoconeActual

variable {G : Type} [Group G]
variable {A B : Type} [CommRing A] [MulSemiringAction G A] [CommRing B]

theorem S3128LocalCoconeMap_invariant (f : A) (hf : forall g : G, g • f = f)
    (u : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
    (hu : forall g : G, (S3128SpecAut (G := G) (A := A) g).hom ≫ u = u)
    (g : G) :
    letI := S3128AwayMulSemiringAction (G := G) (A := A) f hf
    (S3128SpecAut (G := G) (A := Localization.Away f) g).hom ≫
        S3128LocalCoconeMap (A := A) (B := B) f u =
      S3128LocalCoconeMap (A := A) (B := B) f u := by
  letI := S3128AwayMulSemiringAction (G := G) (A := A) f hf
  unfold S3128LocalCoconeMap
  rw [← Category.assoc, ← S3128SpecAut_natural]
  rw [Category.assoc, hu g]

#check S3128LocalCoconeMap_invariant

end LeanFormal.IUT.XiFPaper.S3128LocalCoconeInvariantActual
end