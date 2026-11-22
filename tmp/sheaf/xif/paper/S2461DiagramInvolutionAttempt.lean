import tmp.sheaf.xif.paper.S2459InvolutionSquaredActual
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

noncomputable section
open CategoryTheory Bicategory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S2459InvolutionSquaredActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2461DiagramInvolutionAttempt

local notation "Xf" => S2482Orbicurve.stack.fiber

noncomputable def S2461Map {b b' : Iut.SignActionIndex} (f : b ⟶ b') : Xf ⟶ Xf := by
  cases b with | mk b0 => cases b0
  cases b' with | mk b0 => cases b0
  exact if h : (f.as : Iut.SignGroup) = 1 then � Xf else S2482EllipticInvolution

theorem S2461_signGroup_cases (x : Iut.SignGroup) :
    x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 2) := by
  revert x
  decide

theorem S2461_mul_eq_one {a b : Iut.SignGroup} (ha : a ≠ 1) (hb : b ≠ 1) :
    a * b = 1 := by
  rcases S2461_signGroup_cases a with rfl | rfl
  · exact (ha rfl).elim
  rcases S2461_signGroup_cases b with rfl | rfl
  · exact (hb rfl).elim
  decide

noncomputable def S2461Diagram :
    Iut.SignActionIndex ⥤ᵖ Iut.EtaleStackPseudofunctor F :=
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete
    (fun _ => Xf)
    (fun {b b'} f => S2461Map f)
    (fun b => by
      dsimp [S2461Map]
      rw [dif_pos]
      · rfl
      · rfl)
    (fun {b₀ b₁ b₂} f g => by
      dsimp [S2461Map]
      by_cases hf : (f.as : Iut.SignGroup) = 1
      · rw [dif_pos hf]
        by_cases hg : (g.as : Iut.SignGroup) = 1
        · have hfg : ((f ≫ g).as : Iut.SignGroup) = 1 := by
            rw [LocallyDiscrete.comp_as]
            simp [hf, hg]
          rw [dif_pos hfg, dif_pos hg]
          exact (ρ_ (𝟙 Xf)).symm
        · have hfg : ((f ≫ g).as : Iut.SignGroup) ≠ 1 := by
            rw [LocallyDiscrete.comp_as]
            simp [hf, hg]
          rw [dif_neg hfg, dif_pos hf]
          exact (λ_ S2482EllipticInvolution).symm
      · rw [dif_neg hf]
        by_cases hg : (g.as : Iut.SignGroup) = 1
        · have hfg : ((f ≫ g).as : Iut.SignGroup) ≠ 1 := by
            rw [LocallyDiscrete.comp_as]
            simp [hf, hg]
          rw [dif_neg hfg, dif_pos hg]
          exact (ρ_ S2482EllipticInvolution).symm
        · have hfg : ((f ≫ g).as : Iut.SignGroup) = 1 := by
            rw [LocallyDiscrete.comp_as]
            exact S2461_mul_eq_one hf hg
          rw [dif_pos hfg, dif_neg hf, dif_neg hg]
          exact S2459InvolutionSquared.symm)
    (by cat_disch)
    (by cat_disch)
    (by cat_disch)

#print axioms S2461Diagram

end LeanFormal.IUT.XiFPaper.S2461DiagramInvolutionAttempt

end
