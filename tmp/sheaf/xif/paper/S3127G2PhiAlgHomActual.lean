import tmp.sheaf.xif.paper.S3127G2PhiRingActual
import tmp.sheaf.xif.paper.S3127GammaRAlgebraActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127GammaRAlgebraActual
open LeanFormal.IUT.XiFPaper.S3127G2CoverIsoActual
open LeanFormal.IUT.XiFPaper.S3127G2PhiRingActual
namespace LeanFormal.IUT.XiFPaper.S3127G2PhiAlgHomActual
variable {l : PrimeGeFive}

noncomputable def S3127G2PhiAlgHom
    {A B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B) :
    let R := S1348CoordinateRing l
    letI := gammaAlgebraOf A.obj.left.left A.obj.hom.left
    letI := gammaAlgebraOf B.obj.left.left B.obj.hom.left
    Scheme.Γ.obj (Opposite.op ((S3127G2AffineCoverA B).obj.left)) →ₐ[R]
      Scheme.Γ.obj (Opposite.op ((S3127G2AffineCoverA A).obj.left)) where
  toRingHom := S3127G2PhiRing f
  commutes' := by
    intro r
    rfl

#check S3127G2PhiAlgHom
end LeanFormal.IUT.XiFPaper.S3127G2PhiAlgHomActual
end