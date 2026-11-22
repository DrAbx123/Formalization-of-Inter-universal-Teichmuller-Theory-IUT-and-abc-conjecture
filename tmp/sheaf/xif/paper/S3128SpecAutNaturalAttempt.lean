import tmp.sheaf.xif.paper.S3128LocalCoconeActual

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LeanFormal.IUT.XiFPaper.S3128SpecAutNaturalAttempt

open LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual
open LeanFormal.IUT.XiFPaper.S3128SpecActionActual
open LeanFormal.IUT.XiFPaper.S3128AwayActionActual
open LeanFormal.IUT.XiFPaper.S3128AwayActionHomAttempt

variable {G : Type} [Group G]
variable {A : Type} [CommRing A] [MulSemiringAction G A]

example (f : A) (hf : forall g : G, g • f = f) (g : G) :
    letI := S3128AwayMulSemiringAction (G := G) (A := A) f hf
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) ≫
        (S3128SpecAut (G := G) (A := A) g).hom =
      (S3128SpecAut (G := G) (A := Localization.Away f) g).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) := by
  letI := S3128AwayMulSemiringAction (G := G) (A := A) f hf
  dsimp [S3128SpecAut]
  rw [← Spec.map_comp, ← Spec.map_comp]
  rw [Spec.map_inj]
  ext a
  simp [S3128Away_smul_algebraMap]

end LeanFormal.IUT.XiFPaper.S3128SpecAutNaturalAttempt
end