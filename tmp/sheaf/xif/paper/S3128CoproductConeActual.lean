import tmp.sheaf.xif.paper.S3128PullbackCoproductActual
import tmp.sheaf.xif.paper.S3119StrongTransEqActual
import tmp.sheaf.xif.paper.S1742HomVcompActual

noncomputable section
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.RepresentableCoverChosenCategoryActual
open LeanFormal.IUT.XiFPaper.S3127CoverMorphismActual
open LeanFormal.IUT.XiFPaper.S3128PullbackCoproductActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual
open LeanFormal.IUT.XiFPaper.S3119StrongTransEqActual
open LeanFormal.IUT.XiFPaper.S3121StrongTransVcompActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option checkBinderAnnotations false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S3128CoproductConeActual

variable {l : PrimeGeFive}

/-- The left inclusion into the coproduct cover. -/
noncomputable def S3128CoproductInl (A B : S3127Cover (l := l)) :
    S3127RepMap A (S3128CoproductCover (l := l) A B) where
  hom := Over.homMk (coprod.inl) (by
    show coprod.inl ≫ coprod.desc A.scheme.hom B.scheme.hom = A.scheme.hom
    rw [coprod.inl_desc])
  commutes := by
    let hom : A.scheme ⟶ S3128CoproductScheme (l := l) A B :=
      Over.homMk (coprod.inl) (by
        show coprod.inl ≫ coprod.desc A.scheme.hom B.scheme.hom = A.scheme.hom
        rw [coprod.inl_desc])
    have hdesc : hom ≫ S3128CoproductToScheme (l := l) A B =
        S3128ToSchemeMap (l := l) A := by
      apply Comma.hom_ext
      · change coprod.inl ≫
          coprod.desc (S3128ToSchemeMap A).left (S3128ToSchemeMap B).left =
          (S3128ToSchemeMap A).left
        rw [coprod.inl_desc]
      · exact Subsingleton.elim _ _
    show Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S1348K l) hom)
      (S3128CoproductMap (l := l) A B)) A.map)
    exact ⟨(eqToIso (S3121StrongTransOfHom_vcomp (F := S1348K l) hom
        (S3128CoproductToScheme (l := l) A B))).trans
      ((eqToIso (congrArg (S1742StrongTransOfHom (F := S1348K l)) hdesc)).trans
        (S1742StrongTransIsoOfHom (F := S1348K l) A.map))⟩

/-- The right inclusion into the coproduct cover. -/
noncomputable def S3128CoproductInr (A B : S3127Cover (l := l)) :
    S3127RepMap B (S3128CoproductCover (l := l) A B) where
  hom := Over.homMk (coprod.inr) (by
    show coprod.inr ≫ coprod.desc A.scheme.hom B.scheme.hom = B.scheme.hom
    rw [coprod.inr_desc])
  commutes := by
    let hom : B.scheme ⟶ S3128CoproductScheme (l := l) A B :=
      Over.homMk (coprod.inr) (by
        show coprod.inr ≫ coprod.desc A.scheme.hom B.scheme.hom = B.scheme.hom
        rw [coprod.inr_desc])
    have hdesc : hom ≫ S3128CoproductToScheme (l := l) A B =
        S3128ToSchemeMap (l := l) B := by
      apply Comma.hom_ext
      · change coprod.inr ≫
          coprod.desc (S3128ToSchemeMap A).left (S3128ToSchemeMap B).left =
          (S3128ToSchemeMap B).left
        rw [coprod.inr_desc]
      · exact Subsingleton.elim _ _
    show Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S1348K l) hom)
      (S3128CoproductMap (l := l) A B)) B.map)
    exact ⟨(eqToIso (S3121StrongTransOfHom_vcomp (F := S1348K l) hom
        (S3128CoproductToScheme (l := l) A B))).trans
      ((eqToIso (congrArg (S1742StrongTransOfHom (F := S1348K l)) hdesc)).trans
        (S1742StrongTransIsoOfHom (F := S1348K l) B.map))⟩


/-- The cofan morphism out of the coproduct cover. -/
noncomputable def S3128CoproductDesc {A B C : S3127Cover (l := l)}
    (f : S3127RepMap A C) (g : S3127RepMap B C) :
    S3127RepMap (S3128CoproductCover (l := l) A B) C where
  hom := Over.homMk (coprod.desc f.hom.left g.hom.left) (by
    show coprod.desc f.hom.left g.hom.left ≫ C.scheme.hom =
      coprod.desc A.scheme.hom B.scheme.hom
    apply coprod.hom_ext
    · rw [← Category.assoc, coprod.inl_desc, Over.w, coprod.inl_desc]
    · rw [← Category.assoc, coprod.inr_desc, Over.w, coprod.inr_desc])
  commutes := by
    let hom : S3128CoproductScheme (l := l) A B ⟶ C.scheme :=
      Over.homMk (coprod.desc f.hom.left g.hom.left) (by
        show coprod.desc f.hom.left g.hom.left ≫ C.scheme.hom =
          coprod.desc A.scheme.hom B.scheme.hom
        apply coprod.hom_ext
        · rw [← Category.assoc, coprod.inl_desc, Over.w, coprod.inl_desc]
        · rw [← Category.assoc, coprod.inr_desc, Over.w, coprod.inr_desc])
    have hfH : f.hom.left ≫ (S3128ToSchemeMap (l := l) C).left =
        (S3128ToSchemeMap (l := l) A).left := by
      have h := S1742HomOfStrongTrans_congr (F := S1348K l)
        f.commutes.some
      change S1742HomOfStrongTrans (F := S1348K l)
        (Pseudofunctor.StrongTrans.vcomp
          (S1742StrongTransOfHom (F := S1348K l) f.hom) C.map) =
        S1742HomOfStrongTrans (F := S1348K l) A.map at h
      rw [S1742HomOfStrongTrans_vcomp,
        S1742HomOfStrongTrans_strongTransOfHom] at h
      exact congrArg (fun q => q.left) h
    have hgH : g.hom.left ≫ (S3128ToSchemeMap (l := l) C).left =
        (S3128ToSchemeMap (l := l) B).left := by
      have h := S1742HomOfStrongTrans_congr (F := S1348K l)
        g.commutes.some
      change S1742HomOfStrongTrans (F := S1348K l)
        (Pseudofunctor.StrongTrans.vcomp
          (S1742StrongTransOfHom (F := S1348K l) g.hom) C.map) =
        S1742HomOfStrongTrans (F := S1348K l) B.map at h
      rw [S1742HomOfStrongTrans_vcomp,
        S1742HomOfStrongTrans_strongTransOfHom] at h
      exact congrArg (fun q => q.left) h
    have hH : S1742HomOfStrongTrans (F := S1348K l)
        (Pseudofunctor.StrongTrans.vcomp
          (S1742StrongTransOfHom (F := S1348K l) hom) C.map) =
        S1742HomOfStrongTrans (F := S1348K l)
          (S3128CoproductMap (l := l) A B) := by
      rw [S1742HomOfStrongTrans_vcomp,
        S1742HomOfStrongTrans_strongTransOfHom]
      rw [show S1742HomOfStrongTrans (F := S1348K l)
          (S3128CoproductMap (l := l) A B) =
          S3128CoproductToScheme (l := l) A B from
        S1742HomOfStrongTrans_strongTransOfHom (F := S1348K l) _]
      apply Comma.hom_ext
      · dsimp only [hom]
        change coprod.desc f.hom.left g.hom.left ≫
            (S3128ToSchemeMap (l := l) C).left =
          coprod.desc (S3128ToSchemeMap (l := l) A).left
            (S3128ToSchemeMap (l := l) B).left
        apply coprod.hom_ext
        · rw [← Category.assoc, coprod.inl_desc]
          conv_rhs => rw [coprod.inl_desc]
          exact hfH
        · rw [← Category.assoc, coprod.inr_desc]
          conv_rhs => rw [coprod.inr_desc]
          exact hgH
      · exact Subsingleton.elim _ _
    show Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S1348K l) hom) C.map)
      (S3128CoproductMap (l := l) A B))
    exact ⟨eqToIso (S3119StrongTrans_eq_of_hom_eq (F := S1348K l) _ _ hH)⟩



/-- The binary cofan of two covers. -/
noncomputable def S3128CoproductCofan (A B : S3127Cover (l := l)) :
    BinaryCofan A B :=
  BinaryCofan.mk (S3128CoproductInl (l := l) A B)
    (S3128CoproductInr (l := l) A B)

/-- The left triangle of the coproduct cofan. -/
theorem S3128CoproductInl_desc {A B C : S3127Cover (l := l)}
    (f : S3127RepMap A C) (g : S3127RepMap B C) :
    S3127Comp (S3128CoproductInl (l := l) A B)
      (S3128CoproductDesc (l := l) (A := A) (B := B) f g) = f := by
  apply S3127RepMap_ext
  apply Over.OverMorphism.ext
  dsimp [S3127Comp, S3128CoproductInl, S3128CoproductDesc]
  simp only [Over.homMk_left, Over.comp_left]
  rw [coprod.inl_desc]

/-- The right triangle of the coproduct cofan. -/
theorem S3128CoproductInr_desc {A B C : S3127Cover (l := l)}
    (f : S3127RepMap A C) (g : S3127RepMap B C) :
    S3127Comp (S3128CoproductInr (l := l) A B)
      (S3128CoproductDesc (l := l) (A := A) (B := B) f g) = g := by
  apply S3127RepMap_ext
  apply Over.OverMorphism.ext
  dsimp [S3127Comp, S3128CoproductInr, S3128CoproductDesc]
  simp only [Over.homMk_left, Over.comp_left]
  rw [coprod.inr_desc]

/-- The coproduct cofan is a colimit. -/
noncomputable def S3128CoproductIsColimit (A B : S3127Cover (l := l)) :
    IsColimit (S3128CoproductCofan (l := l) A B) :=
  BinaryCofan.IsColimit.mk (S3128CoproductCofan (l := l) A B)
    (fun f g => S3128CoproductDesc (l := l) f g)
    (fun f g => by
      change S3127Comp (S3128CoproductInl (l := l) A B)
        (S3128CoproductDesc (l := l) (A := A) (B := B) f g) = f
      exact S3128CoproductInl_desc (l := l) f g)
    (fun f g => by
      change S3127Comp (S3128CoproductInr (l := l) A B)
        (S3128CoproductDesc (l := l) (A := A) (B := B) f g) = g
      exact S3128CoproductInr_desc (l := l) f g)
    (by
      intro C f g m h1 h2
      apply S3127RepMap_ext
      apply Over.OverMorphism.ext
      apply coprod.hom_ext
      · have h1' := h1
        change S3127Comp (S3128CoproductCofan (l := l) A B).inl m = f at h1'
        have h1'' : (S3127Comp (S3128CoproductCofan (l := l) A B).inl m).hom =
            f.hom := by
          rw [h1']
        have hd' : (S3127Comp (S3128CoproductInl (l := l) A B)
            (S3128CoproductDesc (l := l) f g)).hom = f.hom :=
          congrArg (fun q : S3127RepMap (l := l) A C => q.hom)
            (S3128CoproductInl_desc (l := l) f g)
        change Over.Hom.left (S3127Comp
            (S3128CoproductCofan (l := l) A B).inl m).hom =
          Over.Hom.left (S3127Comp (S3128CoproductInl (l := l) A B)
            (S3128CoproductDesc (l := l) f g)).hom
        rw [h1'', hd']
      · have h2' := h2
        change S3127Comp (S3128CoproductCofan (l := l) A B).inr m = g at h2'
        have h2'' : (S3127Comp (S3128CoproductCofan (l := l) A B).inr m).hom =
            g.hom := by
          rw [h2']
        have hd' : (S3127Comp (S3128CoproductInr (l := l) A B)
            (S3128CoproductDesc (l := l) f g)).hom = g.hom :=
          congrArg (fun q : S3127RepMap (l := l) B C => q.hom)
            (S3128CoproductInr_desc (l := l) f g)
        change Over.Hom.left (S3127Comp
            (S3128CoproductCofan (l := l) A B).inr m).hom =
          Over.Hom.left (S3127Comp (S3128CoproductInr (l := l) A B)
            (S3128CoproductDesc (l := l) f g)).hom
        rw [h2'', hd']
)



/-- The chosen representable cover category has binary coproducts. -/
noncomputable instance S3128HasBinaryCoproducts :
    HasBinaryCoproducts (S3127Cover (l := l)) := by
  haveI : ∀ {X Y : S3127Cover (l := l)}, HasColimit (pair X Y) :=
    fun {X Y} =>
      HasColimit.mk (ColimitCocone.mk (S3128CoproductCofan (l := l) X Y)
        (S3128CoproductIsColimit (l := l) X Y))
  exact hasBinaryCoproducts_of_hasColimit_pair (S3127Cover (l := l))


#check S3128HasBinaryCoproducts
#check S3128CoproductCofan
#check S3128CoproductInl_desc
#check S3128CoproductInr_desc
#check S3128CoproductIsColimit
#check S3128CoproductDesc
#check S3128CoproductInl
#check S3128CoproductInr

end LeanFormal.IUT.XiFPaper.S3128CoproductConeActual
end