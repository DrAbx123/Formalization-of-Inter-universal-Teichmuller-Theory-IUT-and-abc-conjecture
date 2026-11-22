import tmp.sheaf.xif.paper.S3128TerminalCoverActual
import tmp.sheaf.xif.paper.S3129RepresentableFiniteEtaleActual
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.RepresentableCoverChosenCategoryActual
open LeanFormal.IUT.XiFPaper.S3127CoverMorphismActual
open LeanFormal.IUT.XiFPaper.S3128TerminalCoverActual
open LeanFormal.IUT.XiFPaper.S3129RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S3128PullbackCoproductActual

variable {l : PrimeGeFive}

/-- The scheme-level map underlying a chosen-scheme cover. -/
noncomputable def S3128ToSchemeMap (A : S3127Cover (l := l)) :
    A.scheme ⟶ S1419AffineOver (l := l) :=
  S1742HomOfStrongTrans (F := S1348K l) A.map

/-- The explicit scheme-level pullback of two representable covers. -/
noncomputable def S3128PullbackScheme (A B : S3127Cover (l := l)) :
    SchemeOverField (S1348K l) :=
  S3129PB (F := S1348K l) (S3128ToSchemeMap A) (S3128ToSchemeMap B) B.scheme

/-- The map of the pullback cover to S1536XF. -/
noncomputable def S3128PullbackMap (A B : S3127Cover (l := l)) :
    (S3127Source (l := l) (S3128PullbackScheme A B)).Hom
      (S1536XF (l := l)).stack :=
  S1742StrongTransOfHom (F := S1348K l)
    (S3129PFst (F := S1348K l) (S3128ToSchemeMap A) (S3128ToSchemeMap B) ≫
      S3128ToSchemeMap A)

/-- Exact missing scheme-level finite-etale closure for the pullback cover. -/
def S3128PullbackFiniteEtaleGap (A B : S3127Cover (l := l)) : Prop :=
  AlgebraicGeometry.IsFinite
      (S1742HomOfStrongTrans (F := S1348K l) (S3128PullbackMap A B)).left ∧
    AlgebraicGeometry.Etale
      (S1742HomOfStrongTrans (F := S1348K l) (S3128PullbackMap A B)).left

/-- The pullback gap is inhabited by the scheme-level base-change and
composition instances. -/
theorem S3128PullbackFiniteEtaleGap_proof (A B : S3127Cover (l := l)) :
    S3128PullbackFiniteEtaleGap (l := l) A B := by
  haveI hBfin : AlgebraicGeometry.IsFinite (S3128ToSchemeMap B).left :=
    B.finiteEtale.1
  haveI hBeta : AlgebraicGeometry.Etale (S3128ToSchemeMap B).left :=
    B.finiteEtale.2
  haveI hAfin : AlgebraicGeometry.IsFinite (S3128ToSchemeMap A).left :=
    A.finiteEtale.1
  haveI hAeta : AlgebraicGeometry.Etale (S3128ToSchemeMap A).left :=
    A.finiteEtale.2
  haveI hFstFin : AlgebraicGeometry.IsFinite
      (S3129PFst (F := S1348K l) (S3128ToSchemeMap A) (S3128ToSchemeMap B)).left := by
    change AlgebraicGeometry.IsFinite
      (pullback.fst (S3128ToSchemeMap A).left (S3128ToSchemeMap B).left)
    infer_instance
  haveI hFstEta : AlgebraicGeometry.Etale
      (S3129PFst (F := S1348K l) (S3128ToSchemeMap A) (S3128ToSchemeMap B)).left := by
    change AlgebraicGeometry.Etale
      (pullback.fst (S3128ToSchemeMap A).left (S3128ToSchemeMap B).left)
    infer_instance
  rw [S3128PullbackFiniteEtaleGap, S3128PullbackMap,
    S1742HomOfStrongTrans_strongTransOfHom]
  change AlgebraicGeometry.IsFinite
      ((S3129PFst (F := S1348K l) (S3128ToSchemeMap A)
          (S3128ToSchemeMap B)).left ≫
        (S3128ToSchemeMap A).left) ∧
    AlgebraicGeometry.Etale
      ((S3129PFst (F := S1348K l) (S3128ToSchemeMap A)
          (S3128ToSchemeMap B)).left ≫
        (S3128ToSchemeMap A).left)
  constructor <;> infer_instance

/-- The pullback cover. -/
noncomputable def S3128PullbackCover (A B : S3127Cover (l := l)) :
    S3127Cover (l := l) where
  scheme := S3128PullbackScheme A B
  map := S3128PullbackMap A B
  finiteEtale := S3128PullbackFiniteEtaleGap_proof (l := l) A B


/-- Coproduct of two etale morphisms to the same target is etale. -/
instance S3128EtaleCoprodDesc {X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [AlgebraicGeometry.Etale f] [AlgebraicGeometry.Etale g] :
    AlgebraicGeometry.Etale (coprod.desc f g) := by
  let F : ULift.{0} WalkingPair → Scheme.{0} := fun i => i.1.casesOn X Y
  let h : ∀ i, F i ⟶ Z := fun i => by
    rcases i with ⟨j⟩
    cases j
    · exact f
    · exact g
  have hSigma : AlgebraicGeometry.Etale (Sigma.desc h) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @AlgebraicGeometry.Etale) (fun i => by
      rcases i with ⟨j⟩
      cases j
      · exact inferInstance
      · exact inferInstance)
  have e : CategoryTheory.Arrow.mk (coprod.desc f g) ≅
      CategoryTheory.Arrow.mk (Sigma.desc h) := by
    refine CategoryTheory.Arrow.isoMk (coprodIsoSigma X Y) (Iso.refl Z) ?_
    apply coprod.hom_ext
    · simp only [CategoryTheory.Arrow.mk_hom, CategoryTheory.Iso.refl_hom]
      conv_lhs => rw [← ι_left_coprodIsoSigma_inv (X := X) (Y := Y)]
      have hcomp : (Sigma.ι F ⟨WalkingPair.left⟩ ≫ (coprodIsoSigma X Y).inv) ≫
          (coprodIsoSigma X Y).hom = Sigma.ι F ⟨WalkingPair.left⟩ := by
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      change (Sigma.ι F ⟨WalkingPair.left⟩ ≫ (coprodIsoSigma X Y).inv) ≫
        (coprodIsoSigma X Y).hom ≫ Sigma.desc h =
        coprod.inl ≫ coprod.desc f g ≫ 𝟙 Z
      rw [← Category.assoc, hcomp, Sigma.ι_desc, Category.comp_id, coprod.inl_desc]
    · simp only [CategoryTheory.Arrow.mk_hom, CategoryTheory.Iso.refl_hom]
      conv_lhs => rw [← ι_right_coprodIsoSigma_inv (X := X) (Y := Y)]
      have hcomp : (Sigma.ι F ⟨WalkingPair.right⟩ ≫ (coprodIsoSigma X Y).inv) ≫
          (coprodIsoSigma X Y).hom = Sigma.ι F ⟨WalkingPair.right⟩ := by
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      change (Sigma.ι F ⟨WalkingPair.right⟩ ≫ (coprodIsoSigma X Y).inv) ≫
        (coprodIsoSigma X Y).hom ≫ Sigma.desc h =
        coprod.inr ≫ coprod.desc f g ≫ 𝟙 Z
      rw [← Category.assoc, hcomp, Sigma.ι_desc, Category.comp_id, coprod.inr_desc]
  exact (MorphismProperty.arrow_mk_iso_iff (P := @AlgebraicGeometry.Etale) e).mpr hSigma

/-- The scheme-level coproduct of two representable covers, with its explicit
underlying scheme coproduct. -/
noncomputable abbrev S3128CoproductScheme (A B : S3127Cover (l := l)) :
    SchemeOverField (S1348K l) :=
  Over.mk (coprod.desc A.scheme.hom B.scheme.hom)

@[simp] theorem S3128CoproductScheme_left (A B : S3127Cover (l := l)) :
    (S3128CoproductScheme (l := l) A B).left =
      Limits.coprod A.scheme.left B.scheme.left := rfl

/-- The canonical Over morphism from the coproduct to S1419AffineOver. -/
noncomputable def S3128CoproductToScheme (A B : S3127Cover (l := l)) :
    S3128CoproductScheme A B ⟶ S1419AffineOver (l := l) :=
  Over.homMk (coprod.desc (S3128ToSchemeMap A).left (S3128ToSchemeMap B).left) (by
    show coprod.desc (S3128ToSchemeMap A).left (S3128ToSchemeMap B).left ≫
        (S1419AffineOver (l := l)).hom =
      coprod.desc A.scheme.hom B.scheme.hom
    apply coprod.hom_ext
    · rw [← Category.assoc, coprod.inl_desc]
      conv_rhs => rw [coprod.inl_desc]
      rw [Over.w]
    · rw [← Category.assoc, coprod.inr_desc]
      conv_rhs => rw [coprod.inr_desc]
      rw [Over.w])

/-- The map of the coproduct cover. -/
noncomputable def S3128CoproductMap (A B : S3127Cover (l := l)) :
    (S3127Source (l := l) (S3128CoproductScheme A B)).Hom
      (S1536XF (l := l)).stack :=
  S1742StrongTransOfHom (F := S1348K l) (S3128CoproductToScheme A B)

/-- Scheme-level finite-etale certificate of the coproduct cover. -/
theorem S3128CoproductFiniteEtale (A B : S3127Cover (l := l)) :
    AlgebraicGeometry.IsFinite
        (S1742HomOfStrongTrans (F := S1348K l)
          (S3128CoproductMap A B)).left ∧
      AlgebraicGeometry.Etale
        (S1742HomOfStrongTrans (F := S1348K l)
          (S3128CoproductMap A B)).left := by
  haveI hAfin : AlgebraicGeometry.IsFinite (S3128ToSchemeMap A).left :=
    A.finiteEtale.1
  haveI hAeta : AlgebraicGeometry.Etale (S3128ToSchemeMap A).left :=
    A.finiteEtale.2
  haveI hBfin : AlgebraicGeometry.IsFinite (S3128ToSchemeMap B).left :=
    B.finiteEtale.1
  haveI hBeta : AlgebraicGeometry.Etale (S3128ToSchemeMap B).left :=
    B.finiteEtale.2
  rw [S3128CoproductMap, S1742HomOfStrongTrans_strongTransOfHom]
  change AlgebraicGeometry.IsFinite
      (coprod.desc (S3128ToSchemeMap A).left (S3128ToSchemeMap B).left) ∧
    AlgebraicGeometry.Etale
      (coprod.desc (S3128ToSchemeMap A).left (S3128ToSchemeMap B).left)
  exact ⟨inferInstance, inferInstance⟩

/-- The coproduct cover. -/
noncomputable abbrev S3128CoproductCover (A B : S3127Cover (l := l)) :
    S3127Cover (l := l) where
  scheme := S3128CoproductScheme A B
  map := S3128CoproductMap A B
  finiteEtale := S3128CoproductFiniteEtale (l := l) A B


#check S3128EtaleCoprodDesc
#check S3128CoproductScheme
#check S3128CoproductMap
#check S3128CoproductFiniteEtale
#check S3128CoproductCover
#check S3128ToSchemeMap
#check S3128PullbackScheme
#check S3128PullbackMap
#check S3128PullbackFiniteEtaleGap
#check S3128PullbackFiniteEtaleGap_proof
#check S3128PullbackCover

end LeanFormal.IUT.XiFPaper.S3128PullbackCoproductActual
end