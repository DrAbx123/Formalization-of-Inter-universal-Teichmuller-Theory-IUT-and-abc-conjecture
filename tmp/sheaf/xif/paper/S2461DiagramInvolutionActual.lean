import tmp.sheaf.xif.paper.S2459InvolutionSquaredActual
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

noncomputable section
open CategoryTheory Bicategory
open scoped Pseudofunctor.StrongTrans Bicategory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S2459InvolutionSquaredActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2461DiagramInvolutionActual

local notation "Xf" => S2482Orbicurve.stack.fiber

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
  LocallyDiscrete.mkPseudofunctor
    (fun _ : SingleObj Iut.SignGroup => Xf)
    (fun {b b'} (f : b ⟶ b') => by
      cases b
      cases b'
      let f' : Iut.SignGroup := f
      exact if _h : f' = 1 then CategoryStruct.id Xf else S2482EllipticInvolution)
    (fun b => by
      dsimp
      rw [if_pos]
      · exact Iso.refl _
      · exact SingleObj.id_as_one (M := Iut.SignGroup) b)
    (fun {b₀ b₁ b₂} f g => by
      cases b₀
      cases b₁
      cases b₂
      let f' : Iut.SignGroup := f
      let g' : Iut.SignGroup := g
      let h : Iut.SignGroup := f ≫ g
      have hh : h = g' * f' := rfl
      change (if h = 1 then CategoryStruct.id Xf else S2482EllipticInvolution) ≅
        (if f' = 1 then CategoryStruct.id Xf else S2482EllipticInvolution) ≫
        (if g' = 1 then CategoryStruct.id Xf else S2482EllipticInvolution)
      by_cases hf : f' = 1
      · rw [if_pos hf]
        by_cases hg : g' = 1
        · have hfg : h = 1 := by rw [hh, hf, hg]; simp
          rw [if_pos hfg, if_pos hg]
          exact (Bicategory.rightUnitor (a := Xf) (b := Xf) (CategoryStruct.id Xf)).symm
        · have hfg : h ≠ 1 := by rw [hh, hf]; simpa using hg
          rw [if_neg hfg, if_neg hg]
          exact (Bicategory.leftUnitor (a := Xf) (b := Xf) S2482EllipticInvolution).symm
      · rw [if_neg hf]
        by_cases hg : g' = 1
        · have hfg : h ≠ 1 := by rw [hh, hg]; simpa using hf
          rw [if_neg hfg, if_pos hg]
          exact (Bicategory.rightUnitor (a := Xf) (b := Xf) S2482EllipticInvolution).symm
        · have hfg : h = 1 := by rw [hh]; exact S2461_mul_eq_one hg hf
          rw [if_pos hfg, if_neg hg]
          exact S2459InvolutionSquared.symm)
    (by cat_disch)
    (by cat_disch)
    (by cat_disch)

#print axioms S2461Diagram

end LeanFormal.IUT.XiFPaper.S2461DiagramInvolutionActual

end
