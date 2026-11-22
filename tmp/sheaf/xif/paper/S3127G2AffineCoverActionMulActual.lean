import tmp.sheaf.xif.paper.S3127G2AffineCoverActionActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2CoverIsoActual
open LeanFormal.IUT.XiFPaper.S3127G2AffineCoverActionActual
namespace LeanFormal.IUT.XiFPaper.S3127G2AffineCoverActionMulActual
variable {l : PrimeGeFive} {G : Type} [Group G]

theorem S3127G2AffineCoverAction_mul
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) (g h : G) :
    S3127G2AffineCoverAction A act (g * h) =
      (S3127G2AffineCoverAction A act g).trans
        (S3127G2AffineCoverAction A act h) := by
  ext x
  rfl

#check S3127G2AffineCoverAction_mul
end LeanFormal.IUT.XiFPaper.S3127G2AffineCoverActionMulActual
end