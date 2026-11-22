import tmp.sheaf.xif.paper.S3127FullForgetActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FullForgetActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127FullForgetFunctorActual
variable {l : PrimeGeFive}

noncomputable def S3127FullForget :
    S3127FiniteEtaleOverKFull l ⥤
      FiniteEtaleCover (S1419AffineScheme l) where
  obj := S3127FullForgetObj
  map := S3127FullForgetMap
  map_id X := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl

noncomputable instance S3127FullForget_faithful :
    (S3127FullForget (l := l)).Faithful where
  map_injective := by
    intro X Y f g h
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply Over.OverMorphism.ext
    have hh := congrArg (fun k => k.hom.left) h
    dsimp [S3127FullForgetMap] at hh
    exact hh

#check S3127FullForget_faithful
#check S3127FullForget
end LeanFormal.IUT.XiFPaper.S3127FullForgetFunctorActual
end
