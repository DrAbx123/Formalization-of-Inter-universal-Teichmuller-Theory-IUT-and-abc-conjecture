import tmp.sheaf.xif.paper.S2118PastedComparisonTwistActual
import tmp.sheaf.xif.paper.S1827CloseRetractionActual
import tmp.sheaf.xif.paper.S1801LiftEssSurjActual

noncomputable section
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Probe

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1801LiftEssSurjActual
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S2107RightCancelActual
open LeanFormal.IUT.XiFPaper.S2118PastedComparisonTwistActual

universe u

variable {P X Y Z : EtaleStackPseudofunctor S1726K}
variable {W : EtaleStackPseudofunctor S1726K}

theorem whiskerRight_ident_aux (l : Pseudofunctor.StrongTrans W P)
    (F : Pseudofunctor.StrongTrans P X)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    (Pseudofunctor.StrongTrans.whiskerRight (𝟙 l) F).as.app U
      = 𝟙 (l.app U ≫ F.app U) := by
  have hid : (𝟙 l : Pseudofunctor.StrongTrans.Hom l l)
      = ⟨Pseudofunctor.StrongTrans.Modification.id l⟩ := rfl
  rw [hid]
  change (((⟨Pseudofunctor.StrongTrans.Modification.id l⟩ :
    Pseudofunctor.StrongTrans.Hom l l).as.app U) ▷ (F.app U))
      = 𝟙 (l.app U ≫ F.app U)
  rw [show ((⟨Pseudofunctor.StrongTrans.Modification.id l⟩ :
    Pseudofunctor.StrongTrans.Hom l l).as.app U) = 𝟙 (l.app U) from rfl]
  rw [id_whiskerRight]

theorem S2120Twist_of_liftConeMor_and_full
    (sq : EtalePseudofunctorSquare P X Y Z)
    (w : sq.TwoPullbackWitness)
    (hsub : ∀ {W : EtaleStackPseudofunctor S1726K}
      (a b : Pseudofunctor.StrongTrans W P), Subsingleton (a ⟶ b))
    (hMor : ∀ (W : EtaleStackPseudofunctor S1726K) (c : sq.Cone W),
      Nonempty (sq.ConeMorphism (S2107ImageCone sq (w.lift W c)) c))
    (hFull : S1801TwoCellSurjTo (F := S1726K) w) :
    ∀ (W : EtaleStackPseudofunctor S1726K) (c : sq.Cone W),
      Pseudofunctor.StrongTrans.whiskerRight (w.liftToX W c).hom sq.xToBase ≫ c.commutes.hom =
        (S2107ImageCone sq (w.lift W c)).commutes.hom ≫
          Pseudofunctor.StrongTrans.whiskerRight (w.liftToY W c).hom sq.yToBase := by
  intro W c
  obtain ⟨m⟩ := hMor W c
  obtain ⟨u, huX, huY⟩ := hFull W c (S2107ImageCone sq (w.lift W c)) (w.lift W c) m rfl rfl
  have hu : u = 𝟙 (w.lift W c) := Subsingleton.elim _ _
  have homComp_as : ∀ {F G : EtaleStackPseudofunctor S1726K} {a b c : F ⟶ G}
      (g1 : a ⟶ b) (g2 : b ⟶ c),
      (g1 ≫ g2).as = Pseudofunctor.StrongTrans.Modification.vcomp g1.as g2.as :=
    fun g1 g2 => rfl
  have hXeq : m.toX = (w.liftToX W c).hom := by
    apply Pseudofunctor.StrongTrans.Hom.ext
    apply Pseudofunctor.StrongTrans.Modification.ext
    funext U
    have h := congrArg (fun z => z.as.app U) huX
    rw [hu] at h
    rw [whiskerRight_ident_aux] at h
    simp only [homComp_as, Pseudofunctor.StrongTrans.Modification.vcomp_app,
      Cat.Hom₂.comp_app, eqToHom_refl, Category.id_comp] at h
    -- h : 𝟙 ((w.lift W c).app U ≫ sq.toX.app U) = m.toX.as.app U ≫ (w.liftToX W c).inv.as.app U
    have h' : m.toX.as.app U ≫ (w.liftToX W c).inv.as.app U = 𝟙 _ := h.symm
    calc m.toX.as.app U
        = m.toX.as.app U ≫ (w.liftToX W c).inv.as.app U ≫ (w.liftToX W c).hom.as.app U := by
            rw [Iso.inv_hom_id, Category.comp_id]
      _ = 𝟙 _ ≫ (w.liftToX W c).hom.as.app U := by rw [h']
      _ = (w.liftToX W c).hom.as.app U := Category.id_comp _
  have hYeq : m.toY = (w.liftToY W c).hom := by
    apply Pseudofunctor.StrongTrans.Hom.ext
    apply Pseudofunctor.StrongTrans.Modification.ext
    funext U
    have h := congrArg (fun z => z.as.app U) huY
    rw [hu] at h
    rw [whiskerRight_ident_aux] at h
    simp only [homComp_as, Pseudofunctor.StrongTrans.Modification.vcomp_app,
      Cat.Hom₂.comp_app, eqToHom_refl, Category.id_comp] at h
    have h' : m.toY.as.app U ≫ (w.liftToY W c).inv.as.app U = 𝟙 _ := h.symm
    calc m.toY.as.app U
        = m.toY.as.app U ≫ (w.liftToY W c).inv.as.app U ≫ (w.liftToY W c).hom.as.app U := by
            rw [Iso.inv_hom_id, Category.comp_id]
      _ = 𝟙 _ ≫ (w.liftToY W c).hom.as.app U := by rw [h']
      _ = (w.liftToY W c).hom.as.app U := Category.id_comp _
  rw [hXeq, hYeq] at m
  exact m.compatibility

end Probe
