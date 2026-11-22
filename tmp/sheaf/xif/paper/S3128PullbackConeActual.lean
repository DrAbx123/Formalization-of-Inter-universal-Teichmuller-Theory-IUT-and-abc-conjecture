import tmp.sheaf.xif.paper.S3128InitialConeActual
import tmp.sheaf.xif.paper.S3129RepresentableFiniteEtaleActual

noncomputable section
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.RepresentableCoverChosenCategoryActual
open LeanFormal.IUT.XiFPaper.S3127CoverMorphismActual
open LeanFormal.IUT.XiFPaper.S3128PullbackCoproductActual
open LeanFormal.IUT.XiFPaper.S3129RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual
open LeanFormal.IUT.XiFPaper.S3119StrongTransEqActual
open LeanFormal.IUT.XiFPaper.S3121StrongTransVcompActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S3128PullbackConeActual

variable {l : PrimeGeFive}

/-- The first projection of the pullback cover. -/
noncomputable def S3128PullbackFst (A B : S3127Cover (l := l)) :
    S3127RepMap (S3128PullbackCover (l := l) A B) A where
  hom := S3129PFst (F := S1348K l) (S3128ToSchemeMap A) (S3128ToSchemeMap B)
  commutes := by
    let hom : S3128PullbackScheme (l := l) A B ⟶ A.scheme :=
      S3129PFst (F := S1348K l) (S3128ToSchemeMap A) (S3128ToSchemeMap B)
    have hH : S1742HomOfStrongTrans (F := S1348K l)
        (Pseudofunctor.StrongTrans.vcomp
          (S1742StrongTransOfHom (F := S1348K l) hom) A.map) =
        S1742HomOfStrongTrans (F := S1348K l)
          (S3128PullbackMap (l := l) A B) := by
      rw [S1742HomOfStrongTrans_vcomp,
        S1742HomOfStrongTrans_strongTransOfHom, S3128PullbackMap,
        S1742HomOfStrongTrans_strongTransOfHom]
      rfl
    show Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S1348K l) hom) A.map)
      (S3128PullbackCover (l := l) A B).map)
    exact ⟨eqToIso (S3119StrongTrans_eq_of_hom_eq (F := S1348K l) _ _ hH)⟩

/-- The second projection of the pullback cover. -/
noncomputable def S3128PullbackSnd (A B : S3127Cover (l := l)) :
    S3127RepMap (S3128PullbackCover (l := l) A B) B where
  hom := S3129PSnd (F := S1348K l) (S3128ToSchemeMap A) (S3128ToSchemeMap B)
  commutes := by
    let hom : S3128PullbackScheme (l := l) A B ⟶ B.scheme :=
      S3129PSnd (F := S1348K l) (S3128ToSchemeMap A) (S3128ToSchemeMap B)
    have hcond : S3129PFst (F := S1348K l) (S3128ToSchemeMap A)
        (S3128ToSchemeMap B) ≫ S3128ToSchemeMap A =
        S3129PSnd (F := S1348K l) (S3128ToSchemeMap A)
          (S3128ToSchemeMap B) ≫ S3128ToSchemeMap B := by
      apply Over.OverMorphism.ext
      change pullback.fst (S3128ToSchemeMap A).left
          (S3128ToSchemeMap B).left ≫ (S3128ToSchemeMap A).left =
        pullback.snd (S3128ToSchemeMap A).left
          (S3128ToSchemeMap B).left ≫ (S3128ToSchemeMap B).left
      exact pullback.condition
    have hH : S1742HomOfStrongTrans (F := S1348K l)
        (Pseudofunctor.StrongTrans.vcomp
          (S1742StrongTransOfHom (F := S1348K l) hom) B.map) =
        S1742HomOfStrongTrans (F := S1348K l)
          (S3128PullbackMap (l := l) A B) := by
      rw [S1742HomOfStrongTrans_vcomp,
        S1742HomOfStrongTrans_strongTransOfHom, S3128PullbackMap,
        S1742HomOfStrongTrans_strongTransOfHom]
      exact hcond.symm
    show Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S1348K l) hom) B.map)
      (S3128PullbackCover (l := l) A B).map)
    exact ⟨eqToIso (S3119StrongTrans_eq_of_hom_eq (F := S1348K l) _ _ hH)⟩

#check S3128PullbackFst
#check S3128PullbackSnd

end LeanFormal.IUT.XiFPaper.S3128PullbackConeActual
end