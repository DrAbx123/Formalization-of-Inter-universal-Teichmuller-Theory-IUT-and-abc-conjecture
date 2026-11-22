import tmp.sheaf.xif.paper.S3078PseudofunctorAssemblyActual
noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3078QPrimePseudofunctorTarget
open LeanFormal.IUT.XiFPaper.S3078MapCompNatIsoActual
open LeanFormal.IUT.XiFPaper.S3078PseudofunctorAssemblyActual
open LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
open LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
namespace LeanFormal.IUT.XiFPaper.S3078AssociatorProbe
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

@[simp] theorem S3078PrelaxFunctor_map
    {U V : LocallyDiscrete S3078Kᵒᵖ} (f : U ⟶ V) :
    S3078PrelaxFunctor.map f = (S3078Map f).toCatHom := rfl

@[simp] theorem S3078PrelaxFunctor_map₂
    {U V : LocallyDiscrete S3078Kᵒᵖ} {f g : U ⟶ V}
    (η : f ⟶ g) :
    S3078PrelaxFunctor.map₂ η = (S3078Map₂ η).toCatHom₂ := rfl

@[simp] theorem S3078MapCompNatIso_hom_app {U V W : LocallyDiscrete S3078Kᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) (P : S3048SignTorsorFiber U) :
    (S3078MapCompNatIso f g).hom.app P =
      S3076CompTorsorIsoUnconditionalV3.S3076CompTorsorIsoUnconditionalV3 f g P := rfl

@[simp] theorem S3078MapCompNatIso_inv_app {U V W : LocallyDiscrete S3078Kᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) (P : S3048SignTorsorFiber U) :
    (S3078MapCompNatIso f g).inv.app P =
      S3071TorsorGroupoid.S3071IsoInv W
        (S3076CompTorsorIsoUnconditionalV3.S3076CompTorsorIsoUnconditionalV3 f g P) := rfl

@[simp] theorem S3078MapComp_hom_app_hom {U V W : LocallyDiscrete S3078Kᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) (x : S3048SignTorsorFiber U) :
    ((S3078MapComp f g).hom.toNatTrans.app x).hom =
      (S3076CompTorsorIsoUnconditionalV3.S3076CompTorsorIsoUnconditionalV3 f g x).hom := rfl

@[simp] theorem S3078MapComp_inv_app_hom {U V W : LocallyDiscrete S3078Kᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) (x : S3048SignTorsorFiber U) :
    ((S3078MapComp f g).inv.toNatTrans.app x).hom =
      (S3071TorsorGroupoid.S3071IsoInv W
        (S3076CompTorsorIsoUnconditionalV3.S3076CompTorsorIsoUnconditionalV3 f g x)).hom := rfl

@[simp] theorem S3078MapCompNatIso_hom_app_hom {U V W : LocallyDiscrete S3078Kᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) (x : S3048SignTorsorFiber U) :
    ((S3078MapCompNatIso f g).hom.app x).hom =
      (S3076CompTorsorIsoUnconditionalV3.S3076CompTorsorIsoUnconditionalV3 f g x).hom := rfl

@[simp] theorem S3078MapCompNatIso_inv_app_hom {U V W : LocallyDiscrete S3078Kᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) (x : S3048SignTorsorFiber U) :
    ((S3078MapCompNatIso f g).inv.app x).hom =
      (S3071TorsorGroupoid.S3071IsoInv W
        (S3076CompTorsorIsoUnconditionalV3.S3076CompTorsorIsoUnconditionalV3 f g x)).hom := rfl

@[simp] lemma S3078ToCatHom₂_toNatTrans
    {C D : Type} [Category C] [Category D] {F G : C ⟤ D}
    (η : F ⟶ G) :
    (NatTrans.toCatHom₂ η).toNatTrans = η := rfl

example {a b c d : LocallyDiscrete S3078Kᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    S3078PrelaxFunctor.map₂ (Bicategory.associator f g h).hom =
      (S3078MapComp (f ≫ g) h).hom ≫
        Bicategory.whiskerRight (S3078MapComp f g).hom (S3078PrelaxFunctor.map h) ≫
          (Bicategory.associator (S3078PrelaxFunctor.map f)
            (S3078PrelaxFunctor.map g) (S3078PrelaxFunctor.map h)).hom ≫
            Bicategory.whiskerLeft (S3078PrelaxFunctor.map f) (S3078MapComp g h).inv ≫
              (S3078MapComp f (g ≫ h)).inv := by
  ext x
  apply LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack.S3049TorsorIso.ext
  apply pullback.hom_ext
  · rw [S3078PrelaxFunctor_map₂]
    rw [show S3078Map₂ (Bicategory.associator f g h).hom =
      eqToHom (congrArg S3078Map
        (LocallyDiscrete.eq_of_hom (Bicategory.associator f g h).hom)) from rfl]
    rw [show LocallyDiscrete.eq_of_hom (Bicategory.associator f g h).hom = rfl from
      Subsingleton.elim _ _]
    change ((eqToHom (congrArg S3078Map
      (LocallyDiscrete.eq_of_hom (Bicategory.associator f g h).hom))).toCatHom₂.toNatTrans.app x).hom
      ≫ pullback.fst x.projection (f ≫ g ≫ h).as.unop =
      (((NatTrans.toCatHom₂ (S3078MapCompNatIso (f ≫ g) h).hom ≫
        Bicategory.whiskerRight (NatTrans.toCatHom₂ (S3078MapCompNatIso f g).hom)
          (S3078PrelaxFunctor.map h) ≫
        (Bicategory.associator (S3078PrelaxFunctor.map f)
          (S3078PrelaxFunctor.map g) (S3078PrelaxFunctor.map h)).hom ≫
        Bicategory.whiskerLeft (S3078PrelaxFunctor.map f)
          (NatTrans.toCatHom₂ (S3078MapCompNatIso g h).inv) ≫
        NatTrans.toCatHom₂ (S3078MapCompNatIso f (g ≫ h)).inv).toNatTrans.app x).hom)
      ≫ pullback.fst x.projection (f ≫ g ≫ h).as.unop
    change (𝟙 ((S3078Map ((f ≫ g) ≫ h)).toCatHom.toFunctor.obj x).total)
      ≫ pullback.fst x.projection (f ≫ g ≫ h).as.unop = _
    rw [Category.id_comp]
    simp only [CategoryTheory.Cat.Hom.toNatTrans_comp,
      CategoryTheory.Cat.Hom.toNatTrans_id,
      CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.Hom₂.id_app,
      CategoryTheory.Cat.whiskerRight_toNatTrans,
      CategoryTheory.Cat.whiskerLeft_toNatTrans,
      CategoryTheory.Cat.whiskerRight_app,
      CategoryTheory.Cat.whiskerLeft_app,
      NatTrans.comp_app, S3078ToCatHom₂_toNatTrans,
      LeanFormal.IUT.XiFPaper.S3075QPrimeAssembly.S3049TorsorIso_comp_hom,
      LeanFormal.IUT.XiFPaper.S3075QPrimeAssembly.S3049TorsorIso_id_hom,
      S3078MapCompNatIso_hom_app_hom, S3078MapCompNatIso_inv_app_hom,
      pullback.lift_fst, pullback.lift_snd, Category.assoc]
  · simp only [S3078Map₂, S3078MapComp, Cat.Hom.isoMk, Category.comp_id]

#check S3078PrelaxFunctor.map₂

end LeanFormal.IUT.XiFPaper.S3078AssociatorProbe