import tmp.sheaf.xif.paper.S3127G2QuotientObjActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientObjActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127FullForgetActual
variable {l : PrimeGeFive}

noncomputable def S3127FullForgetObj
    (X : S3127FiniteEtaleOverKFull l) :
    FiniteEtaleCover (S1419AffineScheme l) :=
  ⟨Over.mk X.obj.hom.left, ⟨X.property.2, X.property.1⟩⟩

noncomputable def S3127FullForgetMap
    {X Y : S3127FiniteEtaleOverKFull l} (f : X ⟶ Y) :
    S3127FullForgetObj X ⟶ S3127FullForgetObj Y := by
  refine ObjectProperty.homMk
    (Over.homMk (U := (S3127FullForgetObj X).obj)
      (V := (S3127FullForgetObj Y).obj) f.hom.left.left ?_)
  have h := congrArg
    (fun k : X.obj.left ⟶ S1419AffineOver l => Over.Hom.left k)
    (Over.w f.hom)
  rw [Over.comp_left] at h
  change Over.Hom.left (Over.Hom.left f.hom) ≫
    Over.Hom.left Y.obj.hom = Over.Hom.left X.obj.hom
  exact h

noncomputable def S3127FullForgetRawHom
    {X Y : S3127FiniteEtaleOverKFull l}
    (k : S3127FullForgetObj X ⟶ S3127FullForgetObj Y) :
    (S3127FullForgetObj X).obj.left ⟶ (S3127FullForgetObj Y).obj.left :=
  k.hom.left

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

@[simp] lemma S3127FullForget_map_hom_left
    {X Y : S3127FiniteEtaleOverKFull l} (f : X ⟶ Y) :
    Over.Hom.left ((S3127FullForget (l := l)).map f).hom =
      Over.Hom.left (Over.Hom.left f.hom) := by
  dsimp [S3127FullForget, S3127FullForgetMap]
  rfl

noncomputable instance S3127FullForget_faithful :
    (S3127FullForget (l := l)).Faithful where
  map_injective := by
    intro X Y f g h
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply Over.OverMorphism.ext
    have hh := congrArg (fun k => S3127FullForgetRawHom k) h
    simpa [S3127FullForgetRawHom, S3127FullForgetObj, S3127FullForgetMap,
      S3127FullForget_map_hom_left, Over.mk] using hh

noncomputable instance S3127FullForget_full :
    (S3127FullForget (l := l)).Full where
  map_surjective := by
    intro X Y g
    have hg : g.hom.left ≫ Y.obj.hom.left = X.obj.hom.left :=
      Over.w g.hom
    let k : X.obj.left ⟶ Y.obj.left := Over.homMk g.hom.left (by
      rw [← Over.w X.obj.hom, ← Over.w Y.obj.hom]
      rw [← Category.assoc]
      exact congrArg (fun k => k ≫ (S1419AffineOver l).hom) hg)
    let fhom : X.obj ⟶ Y.obj := Over.homMk k (by
      apply Over.OverMorphism.ext
      exact hg)
    refine ⟨ObjectProperty.homMk fhom, ?_⟩
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl

noncomputable instance S3127FullForget_essSurj :
    (S3127FullForget (l := l)).EssSurj where
  mem_essImage Q := by
    refine ⟨S3127G2QuotientObj Q, ?_⟩
    exact ⟨ObjectProperty.isoMk
      (P := fun X : Over (S1419AffineScheme l) =>
        IsFiniteEtaleHom X.hom)
      (Over.isoMk (Iso.refl _) (by rfl))⟩

noncomputable instance S3127FullForget_isEquivalence :
    (S3127FullForget (l := l)).IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := inferInstance

noncomputable def S3127FullEquivalence :
    S3127FiniteEtaleOverKFull l ≌
      FiniteEtaleCover (S1419AffineScheme l) :=
  (S3127FullForget (l := l)).asEquivalence

theorem S3127FullForget_map_mono
    {X Y : S3127FiniteEtaleOverKFull l} (i : X ⟶ Y) [Mono i] :
    Mono ((S3127FullForget (l := l)).map i) := by
  refine ⟨fun {T} a b h => ?_⟩
  obtain ⟨T', ⟨e⟩⟩ :=
    (S3127FullForget_essSurj (l := l)).mem_essImage T
  obtain ⟨a', ha'⟩ :=
    (S3127FullForget_full (l := l)).map_surjective (e.hom ≫ a)
  obtain ⟨b', hb'⟩ :=
    (S3127FullForget_full (l := l)).map_surjective (e.hom ≫ b)
  have h' : a' ≫ i = b' ≫ i := by
    apply (S3127FullForget_faithful (l := l)).map_injective
    simp only [S3127FullForget.map_comp, ha', hb',
      Category.assoc, h]
  have hai : a' = b' := (cancel_mono i).mp h'
  exact (cancel_epi e.hom).mp (by rw [← ha', ← hb', hai])

#check S3127FullForget_map_mono
#check S3127FullEquivalence
#check S3127FullForget_essSurj
#check S3127FullForget_full
#check S3127FullForget_faithful
#check S3127FullForget
#check S3127FullForgetObj
#check S3127FullForgetMap
end LeanFormal.IUT.XiFPaper.S3127FullForgetActual
end
