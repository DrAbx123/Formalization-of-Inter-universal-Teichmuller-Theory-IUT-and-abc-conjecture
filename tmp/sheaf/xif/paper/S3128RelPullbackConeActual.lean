import tmp.sheaf.xif.paper.S3128PullbackConeActual
import Mathlib.AlgebraicGeometry.Morphisms.Separated

noncomputable section
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.RepresentableCoverChosenCategoryActual
open LeanFormal.IUT.XiFPaper.S3127CoverMorphismActual
open LeanFormal.IUT.XiFPaper.S3128PullbackCoproductActual
open LeanFormal.IUT.XiFPaper.S3129RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S3128PullbackConeActual
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

namespace LeanFormal.IUT.XiFPaper.S3128RelPullbackConeActual

variable {l : PrimeGeFive} {A B C : S3127Cover (l := l)}

/-- A map of chosen covers has finite-etale underlying scheme map. -/
theorem S3128RepMapFiniteEtale (f : S3127RepMap A C) :
    AlgebraicGeometry.IsFinite f.hom.left ∧
      AlgebraicGeometry.Etale f.hom.left := by
  have hH : f.hom.left ≫ (S3128ToSchemeMap (l := l) C).left =
      (S3128ToSchemeMap (l := l) A).left := by
    have h := S1742HomOfStrongTrans_congr (F := S1348K l) f.commutes.some
    change S1742HomOfStrongTrans (F := S1348K l)
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S1348K l) f.hom) C.map) =
        S1742HomOfStrongTrans (F := S1348K l) A.map at h
    rw [S1742HomOfStrongTrans_vcomp,
      S1742HomOfStrongTrans_strongTransOfHom] at h
    exact congrArg (fun q => q.left) h
  haveI hCfin : AlgebraicGeometry.IsFinite
      (S3128ToSchemeMap (l := l) C).left := C.finiteEtale.1
  haveI hCeta : AlgebraicGeometry.Etale
      (S3128ToSchemeMap (l := l) C).left := C.finiteEtale.2
  constructor
  · have hcomp : AlgebraicGeometry.IsFinite
        (f.hom.left ≫ (S3128ToSchemeMap (l := l) C).left) := by
      rw [hH]
      exact A.finiteEtale.1
    exact (AlgebraicGeometry.IsFinite.comp_iff).mp hcomp
  · have hcomp : AlgebraicGeometry.Etale
        (f.hom.left ≫ (S3128ToSchemeMap (l := l) C).left) := by
      rw [hH]
      exact A.finiteEtale.2
    exact AlgebraicGeometry.Etale.of_comp f.hom.left
      (S3128ToSchemeMap (l := l) C).left

/-- The underlying scheme map of a chosen-cover map fits its commuting triangle. -/
theorem S3128RepMap_hom_toSchemeMap (f : S3127RepMap A C) :
    f.hom ≫ S3128ToSchemeMap (l := l) C =
      S3128ToSchemeMap (l := l) A := by
  have h := S1742HomOfStrongTrans_congr (F := S1348K l) f.commutes.some
  change S1742HomOfStrongTrans (F := S1348K l)
    (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S1348K l) f.hom) C.map) =
      S1742HomOfStrongTrans (F := S1348K l) A.map at h
  rw [S1742HomOfStrongTrans_vcomp,
    S1742HomOfStrongTrans_strongTransOfHom] at h
  exact h

/-- The relative pullback scheme of two cover maps. -/
noncomputable abbrev S3128RelPullbackScheme
    (f : S3127RepMap A C) (g : S3127RepMap B C) :
    SchemeOverField (S1348K l) :=
  S3129PB (F := S1348K l) f.hom g.hom B.scheme

/-- The map of the relative pullback cover. -/
noncomputable def S3128RelPullbackMap
    (f : S3127RepMap A C) (g : S3127RepMap B C) :
    (S3127Source (l := l) (S3128RelPullbackScheme (l := l) f g)).Hom
      (S1536XF (l := l)).stack :=
  S1742StrongTransOfHom (F := S1348K l)
    (S3129PFst (F := S1348K l) f.hom g.hom ≫
      S3128ToSchemeMap (l := l) A)

/-- The relative pullback cover. -/
noncomputable abbrev S3128RelPullbackCover
    (f : S3127RepMap A C) (g : S3127RepMap B C) :
    S3127Cover (l := l) where
  scheme := S3128RelPullbackScheme (l := l) f g
  map := S3128RelPullbackMap (l := l) f g
  finiteEtale := by
    haveI hfFin : AlgebraicGeometry.IsFinite f.hom.left :=
      (S3128RepMapFiniteEtale (l := l) f).1
    haveI hfEta : AlgebraicGeometry.Etale f.hom.left :=
      (S3128RepMapFiniteEtale (l := l) f).2
    haveI hgFin : AlgebraicGeometry.IsFinite g.hom.left :=
      (S3128RepMapFiniteEtale (l := l) g).1
    haveI hgEta : AlgebraicGeometry.Etale g.hom.left :=
      (S3128RepMapFiniteEtale (l := l) g).2
    haveI hFstFin : AlgebraicGeometry.IsFinite
        (S3129PFst (F := S1348K l) f.hom g.hom).left := by
      change AlgebraicGeometry.IsFinite
        (pullback.fst f.hom.left g.hom.left)
      infer_instance
    haveI hFstEta : AlgebraicGeometry.Etale
        (S3129PFst (F := S1348K l) f.hom g.hom).left := by
      change AlgebraicGeometry.Etale
        (pullback.fst f.hom.left g.hom.left)
      infer_instance
    haveI hAfin : AlgebraicGeometry.IsFinite
        (S3128ToSchemeMap (l := l) A).left := A.finiteEtale.1
    haveI hAeta : AlgebraicGeometry.Etale
        (S3128ToSchemeMap (l := l) A).left := A.finiteEtale.2
    rw [S3128RelPullbackMap, S1742HomOfStrongTrans_strongTransOfHom]
    change AlgebraicGeometry.IsFinite
        ((S3129PFst (F := S1348K l) f.hom g.hom).left ≫
          (S3128ToSchemeMap (l := l) A).left) ∧
      AlgebraicGeometry.Etale
        ((S3129PFst (F := S1348K l) f.hom g.hom).left ≫
          (S3128ToSchemeMap (l := l) A).left)
    exact ⟨inferInstance, inferInstance⟩


/-- The universal map into the relative pullback cover. -/
noncomputable def S3128RelPullbackLift
    (f : S3127RepMap A C) (g : S3127RepMap B C)
    (s : PullbackCone (f := (show A ⟶ C from f)) (g := (show B ⟶ C from g))) :
    S3127RepMap s.pt (S3128RelPullbackCover (l := l) f g) where
  hom := by
    let sf : S3127RepMap s.pt A := s.fst
    let sg : S3127RepMap s.pt B := s.snd
    have hcond : sf.hom.left ≫ f.hom.left = sg.hom.left ≫ g.hom.left := by
      have h := congrArg (fun q => q.hom.left) (PullbackCone.condition s)
      change Over.Hom.left (S3127Comp s.fst f).hom =
        Over.Hom.left (S3127Comp s.snd g).hom at h
      rw [S3127Comp, Over.comp_left, S3127Comp, Over.comp_left] at h
      simpa using h
    exact Over.homMk (pullback.lift sf.hom.left sg.hom.left hcond) (by
      change pullback.lift sf.hom.left sg.hom.left hcond ≫
          (pullback.fst f.hom.left g.hom.left ≫ A.scheme.hom) =
        s.pt.scheme.hom
      rw [← Category.assoc, pullback.lift_fst]
      exact Over.w sf.hom)
  commutes := by
    let sf : S3127RepMap s.pt A := s.fst
    let sg : S3127RepMap s.pt B := s.snd
    have hcond : sf.hom.left ≫ f.hom.left = sg.hom.left ≫ g.hom.left := by
      have h := congrArg (fun q => q.hom.left) (PullbackCone.condition s)
      change Over.Hom.left (S3127Comp s.fst f).hom =
        Over.Hom.left (S3127Comp s.snd g).hom at h
      rw [S3127Comp, Over.comp_left, S3127Comp, Over.comp_left] at h
      simpa using h
    let liftHom : s.pt.scheme ⟶ S3128RelPullbackScheme (l := l) f g :=
      Over.homMk (pullback.lift sf.hom.left sg.hom.left hcond) (by
        change pullback.lift sf.hom.left sg.hom.left hcond ≫
            (pullback.fst f.hom.left g.hom.left ≫ A.scheme.hom) =
          s.pt.scheme.hom
        rw [← Category.assoc, pullback.lift_fst]
        exact Over.w sf.hom)
    have hlift : liftHom.left = pullback.lift sf.hom.left sg.hom.left hcond := rfl
    have hH : S1742HomOfStrongTrans (F := S1348K l)
        (Pseudofunctor.StrongTrans.vcomp
          (S1742StrongTransOfHom (F := S1348K l) liftHom)
          (S3128RelPullbackMap (l := l) f g)) =
        S1742HomOfStrongTrans (F := S1348K l)
          (Pseudofunctor.StrongTrans.vcomp
            (S1742StrongTransOfHom (F := S1348K l) sf.hom) A.map) := by
      rw [S1742HomOfStrongTrans_vcomp,
        S1742HomOfStrongTrans_strongTransOfHom,
        S1742HomOfStrongTrans_vcomp,
        S1742HomOfStrongTrans_strongTransOfHom,
        S3128RelPullbackMap, S1742HomOfStrongTrans_strongTransOfHom]
      apply Over.OverMorphism.ext
      change (liftHom.left ≫ pullback.fst f.hom.left g.hom.left) ≫
          (S3128ToSchemeMap (l := l) A).left =
        sf.hom.left ≫ (S3128ToSchemeMap (l := l) A).left
      erw [hlift, pullback.lift_fst]
    show Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S1348K l) liftHom)
      (S3128RelPullbackMap (l := l) f g)) s.pt.map)
    exact ⟨(eqToIso (S3119StrongTrans_eq_of_hom_eq (F := S1348K l) _ _ hH)).trans
      sf.commutes.some⟩


/-- The first projection of the relative pullback cover. -/
noncomputable def S3128RelPullbackFst
    (f : S3127RepMap A C) (g : S3127RepMap B C) :
    S3127RepMap (S3128RelPullbackCover (l := l) f g) A where
  hom := S3129PFst (F := S1348K l) f.hom g.hom
  commutes := by
    let hom : S3128RelPullbackScheme (l := l) f g ⟶ A.scheme :=
      S3129PFst (F := S1348K l) f.hom g.hom
    have hH : S1742HomOfStrongTrans (F := S1348K l)
        (Pseudofunctor.StrongTrans.vcomp
          (S1742StrongTransOfHom (F := S1348K l) hom) A.map) =
        S1742HomOfStrongTrans (F := S1348K l)
          (S3128RelPullbackMap (l := l) f g) := by
      rw [S1742HomOfStrongTrans_vcomp,
        S1742HomOfStrongTrans_strongTransOfHom,
        S3128RelPullbackMap, S1742HomOfStrongTrans_strongTransOfHom]
      rfl
    show Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S1348K l) hom) A.map)
      (S3128RelPullbackCover (l := l) f g).map)
    exact ⟨eqToIso (S3119StrongTrans_eq_of_hom_eq (F := S1348K l) _ _ hH)⟩




/-- The second projection of the relative pullback cover. -/
noncomputable def S3128RelPullbackSnd
    (f : S3127RepMap A C) (g : S3127RepMap B C) :
    S3127RepMap (S3128RelPullbackCover (l := l) f g) B where
  hom := S3129PSnd (F := S1348K l) f.hom g.hom
  commutes := by
    let hom : S3128RelPullbackScheme (l := l) f g ⟶ B.scheme :=
      S3129PSnd (F := S1348K l) f.hom g.hom
    have hcond : S3129PFst (F := S1348K l) f.hom g.hom ≫
        S3128ToSchemeMap (l := l) A =
        S3129PSnd (F := S1348K l) f.hom g.hom ≫
          S3128ToSchemeMap (l := l) B := by
      apply Over.OverMorphism.ext
      change pullback.fst f.hom.left g.hom.left ≫
          (S3128ToSchemeMap (l := l) A).left =
        pullback.snd f.hom.left g.hom.left ≫
          (S3128ToSchemeMap (l := l) B).left
      have hf := congrArg (fun q => q.left)
        (S3128RepMap_hom_toSchemeMap (l := l) f)
      rw [Over.comp_left] at hf
      have hg := congrArg (fun q => q.left)
        (S3128RepMap_hom_toSchemeMap (l := l) g)
      rw [Over.comp_left] at hg
      rw [← hf, ← hg]
      rw [← Category.assoc, ← Category.assoc, pullback.condition]
    have hH : S1742HomOfStrongTrans (F := S1348K l)
        (Pseudofunctor.StrongTrans.vcomp
          (S1742StrongTransOfHom (F := S1348K l) hom) B.map) =
        S1742HomOfStrongTrans (F := S1348K l)
          (S3128RelPullbackMap (l := l) f g) := by
      rw [S1742HomOfStrongTrans_vcomp,
        S1742HomOfStrongTrans_strongTransOfHom,
        S3128RelPullbackMap, S1742HomOfStrongTrans_strongTransOfHom]
      exact hcond.symm
    show Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S1348K l) hom) B.map)
      (S3128RelPullbackCover (l := l) f g).map)
    exact ⟨eqToIso (S3119StrongTrans_eq_of_hom_eq (F := S1348K l) _ _ hH)⟩



/-- The relative pullback cone. -/
noncomputable def S3128RelPullbackCone
    (f : S3127RepMap A C) (g : S3127RepMap B C) :
    PullbackCone (show A ⟶ C from f) (show B ⟶ C from g) :=
  PullbackCone.mk (S3128RelPullbackFst (l := l) f g)
    (S3128RelPullbackSnd (l := l) f g)
    (by
      apply S3127RepMap_ext
      apply Over.OverMorphism.ext
      change pullback.fst f.hom.left g.hom.left ≫ f.hom.left =
        pullback.snd f.hom.left g.hom.left ≫ g.hom.left
      exact pullback.condition)




/-- The relative pullback cone is a limit. -/
noncomputable def S3128RelPullbackIsLimit
    (f : S3127RepMap A C) (g : S3127RepMap B C) :
    IsLimit (S3128RelPullbackCone (l := l) f g) :=
  PullbackCone.IsLimit.mk
    (by
      apply S3127RepMap_ext
      apply Over.OverMorphism.ext
      change pullback.fst f.hom.left g.hom.left ≫ f.hom.left =
        pullback.snd f.hom.left g.hom.left ≫ g.hom.left
      exact pullback.condition)
    (fun s => S3128RelPullbackLift f g s)
    (by
      intro s
      apply S3127RepMap_ext
      apply Over.OverMorphism.ext
      dsimp only [S3127Comp, S3128RelPullbackLift, S3128RelPullbackFst,
        S3129PFst, Over.homMk_left, Over.comp_left]
      exact pullback.lift_fst _ _ _)
    (by
      intro s
      apply S3127RepMap_ext
      apply Over.OverMorphism.ext
      dsimp only [S3127Comp, S3128RelPullbackLift, S3128RelPullbackSnd,
        S3129PSnd, Over.homMk_left, Over.comp_left]
      exact pullback.lift_snd _ _ _)
    (by
      intro s m h₁ h₂
      apply S3127RepMap_ext
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · have h := congrArg (fun q => q.hom.left) h₁
        have hcomp : (m ≫ S3128RelPullbackFst (l := l) f g) =
            S3127Comp m (S3128RelPullbackFst (l := l) f g) := rfl
        rw [hcomp, S3127Comp, Over.comp_left] at h
        dsimp only [S3128RelPullbackLift, S3128RelPullbackFst, S3129PFst,
          Over.homMk_left, Over.comp_left] at h ⊢
        simp only [Over.homMk_left] at h ⊢
        exact h.trans (pullback.lift_fst _ _ _).symm
      · have h := congrArg (fun q => q.hom.left) h₂
        have hcomp : (m ≫ S3128RelPullbackSnd (l := l) f g) =
            S3127Comp m (S3128RelPullbackSnd (l := l) f g) := rfl
        rw [hcomp, S3127Comp, Over.comp_left] at h
        dsimp only [S3128RelPullbackLift, S3128RelPullbackSnd, S3129PSnd,
          Over.homMk_left, Over.comp_left] at h ⊢
        simp only [Over.homMk_left] at h ⊢
        exact h.trans (pullback.lift_snd _ _ _).symm)


#check S3128RelPullbackIsLimit

/-- The chosen representable cover category has pullbacks. -/
noncomputable instance S3128HasPullbacks :
    HasPullbacks (S3127Cover (l := l)) := by
  letI : ∀ {X Y Z : S3127Cover (l := l)}
      {f : X ⟶ Z} {g : Y ⟶ Z}, HasLimit (cospan f g) :=
    fun {X Y Z} {f} {g} => by
      let f' : S3127RepMap X Z := f
      let g' : S3127RepMap Y Z := g
      exact HasLimit.mk (LimitCone.mk
        (S3128RelPullbackCone (l := l) f' g')
        (S3128RelPullbackIsLimit (l := l) f' g'))
  exact hasPullbacks_of_hasLimit_cospan (C := S3127Cover (l := l))


#check S3128HasPullbacks
#check S3128RelPullbackCone
#check S3128RelPullbackSnd
#check S3128RelPullbackSnd
#check S3128RepMapFiniteEtale
#check S3128RepMap_hom_toSchemeMap
#check S3128RelPullbackScheme
#check S3128RelPullbackMap
#check S3128RelPullbackCover
#check S3128RelPullbackFst


end LeanFormal.IUT.XiFPaper.S3128RelPullbackConeActual
end