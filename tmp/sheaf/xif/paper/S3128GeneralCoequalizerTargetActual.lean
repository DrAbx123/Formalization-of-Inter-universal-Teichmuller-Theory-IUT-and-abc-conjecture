import tmp.sheaf.xif.paper.S3128AffineCoequalizerActual
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Gluing

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LeanFormal.IUT.XiFPaper.S3128GeneralCoequalizerTargetActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual
open LeanFormal.IUT.XiFPaper.S3128SpecActionActual
open LeanFormal.IUT.XiFPaper.S3128AffineCoequalizerActual

/-- General scheme-level affine quotient cocone target (non-affine T). -/
def S3128GeneralCoequalizerTarget (G : Type) [Group G]
    (A : Type) [CommRing A] [MulSemiringAction G A] (T : Scheme) : Prop :=
  forall (u : Spec (CommRingCat.of A) ⟶ T),
    (forall g : G, (S3128SpecAut (G := G) (A := A) g).hom ≫ u = u) ->
      ∃! (v : Spec (CommRingCat.of (S3128FixedSubring G A)) ⟶ T),
        S3128SpecQuotientMap (G := G) (A := A) ≫ v = u

#check Scheme.affineCover
#check Scheme.OpenCover
#check AlgebraicGeometry.Scheme.Cover.glueMorphisms
#check AlgebraicGeometry.Scheme.Cover.ι_glueMorphisms
#check AlgebraicGeometry.Scheme.Cover.hom_ext
#check IsOpenImmersion.lift
#check S3128GeneralCoequalizerTarget

end LeanFormal.IUT.XiFPaper.S3128GeneralCoequalizerTargetActual
end