import tmp.sheaf.xif.paper.S3128IsLocalizationAwayActual
import tmp.sheaf.xif.paper.S3128LocalAffineQuotientActual
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Gluing

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LeanFormal.IUT.XiFPaper.S3128PrincipalCoverCompatActual

open LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual
open LeanFormal.IUT.XiFPaper.S3128SpecActionActual
open LeanFormal.IUT.XiFPaper.S3128LocalAffineQuotientActual

variable {G : Type} [Group G]
  {A B : Type} [CommRing A] [MulSemiringAction G A]
  [CommRing B] [MulSemiringAction G B]

/-- Compatibility of the quotient with a principal open inclusion:
the diagram
  Spec B --Spec φ--> Spec A
    |                 |
  q_B               q_A
    v                 v
  Spec B^G --fixed--> Spec A^G
commutes. -/
theorem S3128PrincipalCover_compat
    (φ : A →+* B) (hφ : forall (g : G) (a : A),
      φ (g • a) = g • φ a) :
    Spec.map (CommRingCat.ofHom φ) ≫
        S3128SpecQuotientMap (G := G) (A := A) =
      S3128SpecQuotientMap (G := G) (A := B) ≫
        S3128SpecFixedMap (G := G) (A := A) (B := B) φ hφ :=
  S3128SpecQuotientMap_natural (G := G) (A := A) (B := B) φ hφ

#check S3128PrincipalCover_compat
#check AlgebraicGeometry.Scheme.Cover.glueMorphisms
#check AlgebraicGeometry.Scheme.Cover.ι_glueMorphisms

end LeanFormal.IUT.XiFPaper.S3128PrincipalCoverCompatActual
end