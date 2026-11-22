import tmp.sheaf.xif.paper.S3127KLinearFullActual
import tmp.sheaf.xif.paper.S3127GammaRAlgebraActual
import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual
import tmp.sheaf.xif.paper.S1348D6OrbicurveActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127GammaRAlgebraActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2GammaAlgHomActual
variable {l : PrimeGeFive}

noncomputable def gammaRingHomOfFullHom
    {A B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B) :
    Scheme.Γ.obj (Opposite.op B.obj.left.left) →+*
      Scheme.Γ.obj (Opposite.op A.obj.left.left) :=
  (Scheme.Γ.map f.hom.left.left.op).hom

noncomputable def gammaAlgHomOfFullHom
    {A B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B) :
    letI := gammaAlgebraOf B.obj.left.left B.obj.hom.left
    letI := gammaAlgebraOf A.obj.left.left A.obj.hom.left
    Scheme.Γ.obj (Opposite.op B.obj.left.left) →ₐ[S1348CoordinateRing l]
      Scheme.Γ.obj (Opposite.op A.obj.left.left) := by
  let R := S1348CoordinateRing l
  letI := gammaAlgebraOf B.obj.left.left B.obj.hom.left
  letI := gammaAlgebraOf A.obj.left.left A.obj.hom.left
  refine { toRingHom := gammaRingHomOfFullHom f, commutes' := ?_ }
  intro c
  let c' := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom c
  have sq : f.hom.left.left ≫ B.obj.hom.left = A.obj.hom.left :=
    congrArg Over.Hom.left (Over.w f.hom)
  have hsq := congrArg (fun k => Scheme.Γ.map k.op) sq
  erw [op_comp, Scheme.Γ.map_comp] at hsq
  change (Scheme.Γ.map f.hom.left.left.op).hom
      ((Scheme.Γ.map B.obj.hom.left.op).hom c') =
    (Scheme.Γ.map A.obj.hom.left.op).hom c'
  exact congrArg (fun q => q.hom c') hsq

#check gammaRingHomOfFullHom
#check gammaAlgHomOfFullHom
end LeanFormal.IUT.XiFPaper.S3127G2GammaAlgHomActual
end
