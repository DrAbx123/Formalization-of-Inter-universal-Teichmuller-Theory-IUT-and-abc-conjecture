import tmp.sheaf.xif.paper.S2271QHomEqualizerNatActual
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S2259QMapPrecompActual
open LeanFormal.IUT.XiFPaper.S2267QHomEqualizerMulActionActual
open LeanFormal.IUT.XiFPaper.S2271QHomEqualizerNatActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2278QHomNaturalityActual

/-- Global action instance on every point type, matching the action-category
action used by S1971. -/
instance S2278PointMulAction (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ) :
    MulAction Iut.SignGroup (Opposite.unop U.as ⟶ S1726AffineOver) :=
  S1971PointMulAction (U := U)

variable (S : Iut.SchemeOverField S1726K)

instance S2278MulAtS :
    MulAction Iut.SignGroup
      (Opposite.unop (LocallyDiscrete.mk (Opposite.op S)).as ⟶ S1726AffineOver) :=
  S1971PointMulAction (U := LocallyDiscrete.mk (Opposite.op S))

/-- The explicit P_T formula. -/
theorem S2278PT_eq_comp
    (M : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))
    (T : (Over S)ᵒᵖ) :
    S2267PT S M T = T.unop.hom ≫ M.back := by
  unfold S2267PT
  rw [S2259QMap_obj_back]
  rfl

/-- The explicit Q_T formula. -/
theorem S2278QT_eq_comp
    (N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))
    (T : (Over S)ᵒᵖ) :
    S2267QT S N T = T.unop.hom ≫ N.back := by
  unfold S2267QT
  rw [S2259QMap_obj_back]
  rfl

/-- P_T naturality in the slice arrow. -/
theorem S2278PT_natural
    (M : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))
    {T₁ T₂ : (Over S)ᵒᵖ} (p : T₁ ⟶ T₂) :
    p.unop.left ≫ S2267PT S M T₁ = S2267PT S M T₂ := by
  rw [S2278PT_eq_comp S M T₁, S2278PT_eq_comp S M T₂]
  rw [← Category.assoc, Over.w p.unop]

/-- Q_T naturality in the slice arrow. -/
theorem S2278QT_natural
    (N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))
    {T₁ T₂ : (Over S)ᵒᵖ} (p : T₁ ⟶ T₂) :
    p.unop.left ≫ S2267QT S N T₁ = S2267QT S N T₂ := by
  rw [S2278QT_eq_comp S N T₁, S2278QT_eq_comp S N T₂]
  rw [← Category.assoc, Over.w p.unop]

#print axioms S2278PT_eq_comp
#print axioms S2278PT_natural
#print axioms S2278QT_natural

end LeanFormal.IUT.XiFPaper.S2278QHomNaturalityActual

end
