import tmp.sheaf.xif.paper.S3128CoproductConeActual
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

noncomputable section
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.RepresentableCoverChosenCategoryActual
open LeanFormal.IUT.XiFPaper.S3127CoverMorphismActual
open LeanFormal.IUT.XiFPaper.S3128PullbackCoproductActual
open LeanFormal.IUT.XiFPaper.S3128CoproductConeActual
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

namespace LeanFormal.IUT.XiFPaper.S3128InitialConeActual

variable {l : PrimeGeFive}

/-- The empty scheme over the base field. -/
noncomputable def S3128EmptyOver : SchemeOverField (S1348K l) :=
  Over.mk (Scheme.emptyTo (Spec (CommRingCat.of (S1348K l))))

/-- The empty Over morphism to the affine terminal object. -/
noncomputable def S3128EmptyToAffine :
    S3128EmptyOver (l := l) ⟶ S1419AffineOver (l := l) :=
  Over.homMk (Scheme.emptyTo (S1419AffineOver (l := l)).left)
    (Scheme.empty_ext _ _)

/-- The initial cover: empty scheme with the empty map to S1536XF. -/
noncomputable def S3128InitialCover : S3127Cover (l := l) where
  scheme := S3128EmptyOver (l := l)
  map := S1742StrongTransOfHom (F := S1348K l)
    (S3128EmptyToAffine (l := l))
  finiteEtale := by
    rw [S1742HomOfStrongTrans_strongTransOfHom]
    change AlgebraicGeometry.IsFinite
        (Scheme.emptyTo (S1419AffineOver (l := l)).left) ∧
      AlgebraicGeometry.Etale (Scheme.emptyTo (S1419AffineOver (l := l)).left)
    exact ⟨inferInstance, inferInstance⟩

/-- The unique map from the initial cover to any cover. -/
noncomputable def S3128InitialHom (A : S3127Cover (l := l)) :
    S3127RepMap (S3128InitialCover (l := l)) A where
  hom := Over.homMk (Scheme.emptyTo A.scheme.left) (by
    apply Scheme.empty_ext)
  commutes := by
    let hom : S3128EmptyOver (l := l) ⟶ A.scheme :=
      Over.homMk (Scheme.emptyTo A.scheme.left) (by apply Scheme.empty_ext)
    let Ato : Pseudofunctor.StrongTrans
        (S1742YS (F := S1348K l) A.scheme)
        (S1742YS (F := S1348K l) (S1419AffineOver (l := l))) := A.map
    have hH : S1742HomOfStrongTrans (F := S1348K l)
        (Pseudofunctor.StrongTrans.vcomp
          (S1742StrongTransOfHom (F := S1348K l) hom) Ato) =
        S1742HomOfStrongTrans (F := S1348K l)
          (S1742StrongTransOfHom (F := S1348K l)
            (S3128EmptyToAffine (l := l))) := by
      rw [S1742HomOfStrongTrans_vcomp,
        S1742HomOfStrongTrans_strongTransOfHom,
        S1742HomOfStrongTrans_strongTransOfHom]
      apply Over.OverMorphism.ext
      apply Scheme.empty_ext
    show Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S1348K l) hom) A.map)
      (S3128InitialCover (l := l)).map)
    exact ⟨eqToIso (S3119StrongTrans_eq_of_hom_eq (F := S1348K l) _ _ hH)⟩

/-- Uniqueness of maps out of the initial cover. -/
theorem S3128InitialHom_unique (A : S3127Cover (l := l))
    (f : S3127RepMap (S3128InitialCover (l := l)) A) :
    f = S3128InitialHom (l := l) A := by
  apply S3127RepMap_ext
  apply Over.OverMorphism.ext
  exact Scheme.empty_ext _ _

/-- The initial cover is initial. -/
noncomputable def S3128Initial_isInitial :
    IsInitial (S3128InitialCover (l := l)) :=
  IsInitial.ofUniqueHom (fun A => S3128InitialHom (l := l) A)
    (fun A f => S3128InitialHom_unique (l := l) A f)

/-- The chosen representable cover category has an initial object. -/
noncomputable instance S3128HasInitial :
    HasInitial (S3127Cover (l := l)) :=
  S3128Initial_isInitial (l := l) |>.hasInitial

/-- The chosen representable cover category has finite coproducts. -/
noncomputable instance S3128HasFiniteCoproducts :
    HasFiniteCoproducts (S3127Cover (l := l)) :=
  hasFiniteCoproducts_of_has_binary_and_initial

#check S3128EmptyOver
#check S3128InitialCover
#check S3128InitialHom
#check S3128InitialHom_unique
#check S3128Initial_isInitial
#check S3128HasInitial
#check S3128HasFiniteCoproducts

end LeanFormal.IUT.XiFPaper.S3128InitialConeActual
end