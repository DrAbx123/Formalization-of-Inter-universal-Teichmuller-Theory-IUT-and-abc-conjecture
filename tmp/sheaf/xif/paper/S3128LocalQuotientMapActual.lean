import tmp.sheaf.xif.paper.S3128LocalCoconeInvariantActual
import tmp.sheaf.xif.paper.S3128AffineCoequalizerActual

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LeanFormal.IUT.XiFPaper.S3128LocalQuotientMapActual

open LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual
open LeanFormal.IUT.XiFPaper.S3128SpecActionActual
open LeanFormal.IUT.XiFPaper.S3128AwayActionActual
open LeanFormal.IUT.XiFPaper.S3128AwayActionHomAttempt
open LeanFormal.IUT.XiFPaper.S3128SpecAutNaturalActual
open LeanFormal.IUT.XiFPaper.S3128LocalCoconeActual
open LeanFormal.IUT.XiFPaper.S3128LocalCoconeInvariantActual
open LeanFormal.IUT.XiFPaper.S3128AffineCoequalizerActual

variable {G : Type} [Group G]
variable {A B : Type} [CommRing A] [MulSemiringAction G A] [CommRing B]

theorem S3128LocalQuotientMap_exists (f : A) (hf : forall g : G, g • f = f)
    (u : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
    (hu : forall g : G, (S3128SpecAut (G := G) (A := A) g).hom ≫ u = u) :
    letI := S3128AwayMulSemiringAction (G := G) (A := A) f hf
    ∃ v : Spec (CommRingCat.of (S3128FixedSubring G (Localization.Away f))) ⟶
        Spec (CommRingCat.of B),
      S3128SpecQuotientMap (G := G) (A := Localization.Away f) ≫ v =
        S3128LocalCoconeMap (A := A) (B := B) f u := by
  letI := S3128AwayMulSemiringAction (G := G) (A := A) f hf
  rcases S3128AffineCoconeTarget_holds (G := G) (A := Localization.Away f) (B := B)
    (S3128LocalCoconeMap (A := A) (B := B) f u)
    (S3128LocalCoconeMap_invariant f hf u hu) with ⟨v, hv, _⟩
  exact ⟨v, hv⟩

#check S3128LocalQuotientMap_exists

end LeanFormal.IUT.XiFPaper.S3128LocalQuotientMapActual
end