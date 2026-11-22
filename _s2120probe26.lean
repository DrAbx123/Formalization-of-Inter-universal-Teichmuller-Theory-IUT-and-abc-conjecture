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

theorem eq_hom_of_comp_inv_eq_id {C : Type*} [Category C] {A B : C} (a : A ⟶ B)
    (e : A ≅ B) (h : a ≫ e.inv = 𝟙 A) : a = e.hom := by
  calc a = a ≫ 𝟙 B := (Category.comp_id a).symm
    _ = a ≫ (e.inv ≫ e.hom) := by rw [Iso.inv_hom_id]
    _ = (a ≫ e.inv) ≫ e.hom := by rw [Category.assoc]
    _ = 𝟙 A ≫ e.hom := by rw [h]
    _ = e.hom := Category.id_comp e.hom

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

theorem whiskerRight_ident (l : Pseudofunctor.StrongTrans W P)
    (F : Pseudofunctor.StrongTrans P X) :
    Pseudofunctor.StrongTrans.whiskerRight (𝟙 l) F =
      𝟙 (Pseudofunctor.StrongTrans.vcomp l F) := by
  apply Pseudofunctor.StrongTrans.Hom.ext
  apply Pseudofunctor.StrongTrans.Modification.ext
  funext U
  rw [show (Pseudofunctor.StrongTrans.whiskerRight (𝟙 l) F).as.app U
      = 𝟙 (l.app U ≫ F.app U) from whiskerRight_ident_aux l F U]
  conv_rhs =>
    rw [show (𝟙 (Pseudofunctor.StrongTrans.vcomp l F))
      = (⟨Pseudofunctor.StrongTrans.Modification.id
          (Pseudofunctor.StrongTrans.vcomp l F)⟩ :
          Pseudofunctor.StrongTrans.Hom (Pseudofunctor.StrongTrans.vcomp l F)
            (Pseudofunctor.StrongTrans.vcomp l F)) from rfl]
  rfl

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
  have hu : u = 𝟙 (w.lift W c) := @Subsingleton.elim _ (hsub (w.lift W c) (w.lift W c)) _ _
  have hXeq : m.toX = (w.liftToX W c).hom := by
    have h := huX
    rw [hu] at h
    rw [whiskerRight_ident] at h
    simp only [eqToHom_refl, Category.id_comp] at h
    exact eq_hom_of_comp_inv_eq_id m.toX (w.liftToX W c) (h.symm)
  have hYeq : m.toY = (w.liftToY W c).hom := by
    have h := huY
    rw [hu] at h
    rw [whiskerRight_ident] at h
    simp only [eqToHom_refl, Category.id_comp] at h
    exact eq_hom_of_comp_inv_eq_id m.toY (w.liftToY W c) (h.symm)
  rw [← hXeq, ← hYeq]
  exact m.compatibility

end Probe
