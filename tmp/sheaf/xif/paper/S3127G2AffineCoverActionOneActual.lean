import tmp.sheaf.xif.paper.S3127G2AffineCoverActionActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2CoverIsoActual
open LeanFormal.IUT.XiFPaper.S3127G2AffineCoverActionActual
namespace LeanFormal.IUT.XiFPaper.S3127G2AffineCoverActionOneActual
variable {l : PrimeGeFive} {G : Type} [Group G]

theorem S3127G2AffineCoverAction_one
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) :
    S3127G2AffineCoverAction A act (1 : G) =
      Iso.refl (S3127G2AffineCoverA A) := by
  rfl

#check S3127G2AffineCoverAction_one
end LeanFormal.IUT.XiFPaper.S3127G2AffineCoverActionOneActual
end