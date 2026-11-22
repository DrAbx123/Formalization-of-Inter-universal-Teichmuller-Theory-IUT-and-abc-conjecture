import tmp.sheaf.xif.paper.S1893PullbackUniversalActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
namespace LeanFormal.IUT.XiFPaper.S1985Probe

universe u

theorem coneHom_isIso {A B C X : Type u} [Category.{u, u} A] [Category.{u, u} B]
    [Category.{u, u} C] [Category.{u, u} X] {L : A ⥤ C} {R : B ⥤ C}
    {c₁ c₂ : LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual.S1893Cone L R X}
    (m : LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual.S1893Cone.Hom c₁ c₂)
    [IsIso m.toA] [IsIso m.toB] : IsIso (C := LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual.S1893Cone L R X) m := by
  let invA : c₂.toA ⟶ c₁.toA := inv m.toA
  let invB : c₂.toB ⟶ c₁.toB := inv m.toB
  have hcomp : Functor.whiskerRight invA L ≫ c₁.commutes.hom =
      c₂.commutes.hom ≫ Functor.whiskerRight invB R := by
    have hm := m.2
    have hα : Functor.whiskerRight invA L = inv (Functor.whiskerRight m.toA L) := by
      dsimp [invA]
      simp
    have hβ : Functor.whiskerRight invB R = inv (Functor.whiskerRight m.toB R) := by
      dsimp [invB]
      simp
    rw [hα, hβ]
    have hf : c₁.commutes.hom = Functor.whiskerRight m.toA L ≫ c₂.commutes.hom ≫
        inv (Functor.whiskerRight m.toB R) := by
      calc
        c₁.commutes.hom = (c₁.commutes.hom ≫ Functor.whiskerRight m.toB R) ≫
            inv (Functor.whiskerRight m.toB R) := by
          rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
        _ = (Functor.whiskerRight m.toA L ≫ c₂.commutes.hom) ≫
            inv (Functor.whiskerRight m.toB R) := by rw [← hm]
        _ = Functor.whiskerRight m.toA L ≫ c₂.commutes.hom ≫
            inv (Functor.whiskerRight m.toB R) := by simp only [Category.assoc]
    calc
      inv (Functor.whiskerRight m.toA L) ≫ c₁.commutes.hom =
          inv (Functor.whiskerRight m.toA L) ≫
            (Functor.whiskerRight m.toA L ≫ c₂.commutes.hom ≫
              inv (Functor.whiskerRight m.toB R)) := by rw [hf]
      _ = c₂.commutes.hom ≫ inv (Functor.whiskerRight m.toB R) := by
        simp only [← Category.assoc]
        rw [← hα, ← Functor.whiskerRight_comp]
        rw [show invA ≫ m.toA = 𝟙 c₂.toA by dsimp [invA]; simp]
        rw [Functor.whiskerRight_id']
        simp
  let inv' : LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual.S1893Cone.Hom c₂ c₁ :=
    ⟨(invA, invB), hcomp⟩
  refine ⟨inv', ?_, ?_⟩
  · apply LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual.S1893Cone.Hom.ext
    · change m.toA ≫ invA = 𝟙 c₁.toA
      dsimp [invA]
      simp
    · change m.toB ≫ invB = 𝟙 c₁.toB
      dsimp [invB]
      simp
  · apply LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual.S1893Cone.Hom.ext
    · change invA ≫ m.toA = 𝟙 c₂.toA
      dsimp [invA]
      simp
    · change invB ≫ m.toB = 𝟙 c₂.toB
      dsimp [invB]
      simp

end LeanFormal.IUT.XiFPaper.S1985Probe