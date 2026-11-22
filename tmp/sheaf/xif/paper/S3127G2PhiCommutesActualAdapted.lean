import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127FullForgetActual
import tmp.sheaf.xif.paper.S3127GammaRAlgebraActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127GammaRAlgebraActual
open LeanFormal.IUT.XiFPaper.S3127G2CoverIsoActual
open LeanFormal.IUT.XiFPaper.S3127FullForgetActual
namespace LeanFormal.IUT.XiFPaper.S3127G2PhiCommutesActualAdapted
variable {l : PrimeGeFive}

noncomputable def S3127G2PhiRingLocal
    {A B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B) :
    Scheme.Γ.obj (Opposite.op ((S3127G2AffineCoverA B).obj.left)) ⟶
      Scheme.Γ.obj (Opposite.op ((S3127G2AffineCoverA A).obj.left)) :=
  let f_aff :=
    (S3127G2CoverIsoA A).inv ≫ S3127FullForget.map f ≫
      (S3127G2CoverIsoA B).hom
  Scheme.Γ.map f_aff.hom.left.op

theorem S3127G2PhiRingLocal_commutes
    {A B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B) (c : S1348CoordinateRing l) :
    let R := S1348CoordinateRing l
    letI := gammaAlgebraOf A.obj.left.left A.obj.hom.left
    letI := gammaAlgebraOf B.obj.left.left B.obj.hom.left
    S3127G2PhiRingLocal f
      (algebraMap R (Scheme.Γ.obj (Opposite.op ((S3127G2AffineCoverA B).obj.left))) c) =
    algebraMap R (Scheme.Γ.obj (Opposite.op ((S3127G2AffineCoverA A).obj.left))) c := by
  dsimp only
  rfl

#check S3127G2PhiRingLocal_commutes
end LeanFormal.IUT.XiFPaper.S3127G2PhiCommutesActualAdapted
end