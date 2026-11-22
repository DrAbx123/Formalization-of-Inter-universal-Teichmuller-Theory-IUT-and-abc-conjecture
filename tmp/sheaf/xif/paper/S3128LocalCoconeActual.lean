import tmp.sheaf.xif.paper.S3128AwayActionHomAttempt
import tmp.sheaf.xif.paper.S3128AffineCoequalizerActual
import Mathlib.AlgebraicGeometry.Cover.Open

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LeanFormal.IUT.XiFPaper.S3128LocalCoconeActual

open LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual
open LeanFormal.IUT.XiFPaper.S3128SpecActionActual
open LeanFormal.IUT.XiFPaper.S3128AwayActionActual
open LeanFormal.IUT.XiFPaper.S3128AwayActionHomAttempt
open LeanFormal.IUT.XiFPaper.S3128AwayRingEquivAttempt

variable {G : Type} [Group G]
variable {A B : Type} [CommRing A] [MulSemiringAction G A] [CommRing B]

/-- Restriction of a cocone u : Spec A → Spec B to Spec (A_f). -/
noncomputable def S3128LocalCoconeMap (f : A) [Algebra A (Localization.Away f)]
    (u : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B)) :
    Spec (CommRingCat.of (Localization.Away f)) ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) ≫ u

#check S3128LocalCoconeMap

end LeanFormal.IUT.XiFPaper.S3128LocalCoconeActual
end