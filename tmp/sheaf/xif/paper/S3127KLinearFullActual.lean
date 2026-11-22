import tmp.sheaf.xif.paper.S3127ForgetfulActual
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127ForgetfulActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
variable {l : PrimeGeFive}

abbrev S3127FiniteEtaleOverKFull (l : PrimeGeFive) : Type 1 :=
  ObjectProperty.FullSubcategory
    (fun Y : Over (S1419AffineOver l) =>
      IsFinite Y.hom.left ∧ Etale Y.hom.left)

noncomputable def S3127OldOfNew
    (Y : S3127FiniteEtaleOverKFull l) :
    S3127FiniteEtaleOverK (l := l) where
  obj := Y.obj
  finiteEtale := Y.property

noncomputable def S3127NewOfOld
    (Y : S3127FiniteEtaleOverK (l := l)) :
    S3127FiniteEtaleOverKFull l :=
  ⟨Y.obj, Y.finiteEtale⟩

noncomputable def S3127OldToNewFunctor :
    S3127FiniteEtaleOverK (l := l) ⥤ S3127FiniteEtaleOverKFull l where
  obj := S3127NewOfOld
  map f := ObjectProperty.homMk f
  map_id A := by
    apply ObjectProperty.hom_ext
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    rfl

noncomputable instance S3127OldToNewFunctor_full :
    (S3127OldToNewFunctor (l := l)).Full where
  map_surjective := by
    intro A B g
    exact ⟨g.hom, by
      apply ObjectProperty.hom_ext
      rfl⟩

noncomputable instance S3127OldToNewFunctor_faithful :
    (S3127OldToNewFunctor (l := l)).Faithful where
  map_injective := by
    intro A B f g h
    exact congrArg (fun k => k.hom) h

noncomputable instance S3127OldToNewFunctor_essSurj :
    (S3127OldToNewFunctor (l := l)).EssSurj where
  mem_essImage Y := by
    refine ⟨S3127OldOfNew Y, ?_⟩
    exact ⟨Iso.refl _⟩

noncomputable instance S3127OldToNewFunctor_isEquivalence :
    (S3127OldToNewFunctor (l := l)).IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := inferInstance

noncomputable def S3127OldNewEquivalence :
    S3127FiniteEtaleOverK (l := l) ≌ S3127FiniteEtaleOverKFull l :=
  (S3127OldToNewFunctor (l := l)).asEquivalence

#check S3127OldNewEquivalence
#check S3127FiniteEtaleOverKFull
#check S3127OldToNewFunctor
#check S3127OldToNewFunctor_full
#check S3127OldToNewFunctor_faithful
#check S3127OldToNewFunctor_essSurj
end LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
end
