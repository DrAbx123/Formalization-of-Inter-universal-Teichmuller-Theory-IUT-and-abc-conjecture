import tmp.sheaf.xif.paper.S2464UnitorProbe
import tmp.sheaf.xif.paper.S2459InvolutionSquaredActual

noncomputable section
open CategoryTheory Bicategory
open scoped Pseudofunctor.StrongTrans Bicategory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S2459InvolutionSquaredActual
open LeanFormal.IUT.XiFPaper.S2464UnitorProbe
set_option synthInstance.maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2465MapCompLemmasActual
local notation "Xf" => S2482Orbicurve.stack.fiber

noncomputable def S2465Map (s : Iut.SignGroup) : Xf ⟶ Xf :=
  if s = 1 then CategoryStruct.id Xf else S2482EllipticInvolution

theorem S2465_signGroup_cases (x : Iut.SignGroup) :
    x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 2) := by
  revert x
  decide

theorem S2465_mul_eq_one {a b : Iut.SignGroup} (ha : a ≠ 1) (hb : b ≠ 1) :
    a * b = 1 := by
  rcases S2465_signGroup_cases a with rfl | rfl
  · exact (ha rfl).elim
  rcases S2465_signGroup_cases b with rfl | rfl
  · exact (hb rfl).elim
  decide

noncomputable def S2465_comp_id_id (f g : Iut.SignGroup) (hf : f = 1) (hg : g = 1) :
    S2465Map (g * f) ≅ S2465Map f ≫ S2465Map g := by
  subst f; subst g
  simp only [mul_one]
  dsimp [S2465Map]
  exact (Bicategory.rightUnitor (a := Xf) (b := Xf) (CategoryStruct.id Xf)).symm

noncomputable def S2465_comp_id_nonid (f g : Iut.SignGroup) (hf : f = 1) (hg : g ≠ 1) :
    S2465Map (g * f) ≅ S2465Map f ≫ S2465Map g := by
  subst f
  rw [mul_one]
  dsimp [S2465Map]
  rw [if_neg hg]
  exact (Bicategory.leftUnitor (a := Xf) (b := Xf) S2482EllipticInvolution).symm

noncomputable def S2465_comp_nonid_id (f g : Iut.SignGroup) (hf : f ≠ 1) (hg : g = 1) :
    S2465Map (g * f) ≅ S2465Map f ≫ S2465Map g := by
  subst g
  rw [one_mul]
  dsimp [S2465Map]
  rw [if_neg hf]
  exact (Bicategory.rightUnitor (a := Xf) (b := Xf) S2482EllipticInvolution).symm

noncomputable def S2465_comp_nonid_nonid (f g : Iut.SignGroup) (hf : f ≠ 1) (hg : g ≠ 1) :
    S2465Map (g * f) ≅ S2465Map f ≫ S2465Map g := by
  have hfg : g * f = 1 := S2465_mul_eq_one hg hf
  dsimp [S2465Map]
  rw [if_pos hfg]
  rw [if_neg hf]
  rw [if_neg hg]
  exact S2459InvolutionSquared.symm

#print axioms S2465_comp_id_id
#print axioms S2465_comp_id_nonid
#print axioms S2465_comp_nonid_id
#print axioms S2465_comp_nonid_nonid

end LeanFormal.IUT.XiFPaper.S2465MapCompLemmasActual
end
