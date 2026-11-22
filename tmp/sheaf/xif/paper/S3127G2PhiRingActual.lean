import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127FullForgetActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127G2CoverIsoActual
open LeanFormal.IUT.XiFPaper.S3127FullForgetActual
namespace LeanFormal.IUT.XiFPaper.S3127G2PhiRingActual
variable {l : PrimeGeFive}

/-- Ring map on affine cover sections induced by a morphism of full covers. -/
noncomputable def S3127G2PhiRing
    {A B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B) :
    Scheme.Γ.obj (Opposite.op ((S3127G2AffineCoverA B).obj.left)) ⟶
      Scheme.Γ.obj (Opposite.op ((S3127G2AffineCoverA A).obj.left)) :=
  let f_aff :=
    (S3127G2CoverIsoA A).inv ≫ S3127FullForget.map f ≫
      (S3127G2CoverIsoA B).hom
  Scheme.Γ.map f_aff.hom.left.op

#check S3127G2PhiRing
end LeanFormal.IUT.XiFPaper.S3127G2PhiRingActual
end