import tmp.sheaf.xif.paper.S2259QMapPrecompActual
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2267QHomEqualizerMulActionActual

variable (S : Iut.SchemeOverField S1726K)

/-- The point type of the action category at T, written exactly as it appears
in the .back field. -/
abbrev S2267Point (T : (Over S)ᵒᵖ) : Type :=
  Opposite.unop (LocallyDiscrete.mk (Opposite.op T.unop.left)).as ⟶ S1726AffineOver

/-- The explicit action on the point type: postcomposition with the sign scheme
automorphism. -/
def S2267smul {T : (Over S)ᵒᵖ} (g : Iut.SignGroup) (P : S2267Point S T) :
    S2267Point S T :=
  P ≫ S1971SchemeAut g

/-- The explicit smul agrees with the action-category smul formula. -/
instance S2267PointMulAction (T : (Over S)ᵒᵖ) :
    MulAction Iut.SignGroup (S2267Point S T) where
  smul := S2267smul S
  one_smul P := by
    change P ≫ S1971SchemeAut 1 = P
    rw [S1971SchemeAut_one, Category.comp_id]
  mul_smul g h P := by
    change P ≫ S1971SchemeAut (g * h) = P ≫ S1971SchemeAut h ≫ S1971SchemeAut g
    rw [S1971SchemeAut_mul]

/-- The underlying affine morphism P_T. -/
noncomputable def S2267PT
    (M : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))
    (T : (Over S)ᵒᵖ) : S2267Point S T :=
  ((S2152Q.map (T.unop.hom.op).toLoc).toFunctor.obj M).back

/-- The underlying affine morphism Q_T. -/
noncomputable def S2267QT
    (N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))
    (T : (Over S)ᵒᵖ) : S2267Point S T :=
  ((S2152Q.map (T.unop.hom.op).toLoc).toFunctor.obj N).back

/-- Pointwise f map: g maps to g smul P_T. -/
def S2267fPoint
    (M : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))
    (T : (Over S)ᵒᵖ) (g : Iut.SignGroup) : S2267Point S T :=
  g • S2267PT S M T

/-- Pointwise g map: constant Q_T. -/
def S2267gPoint
    (N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))
    (T : (Over S)ᵒᵖ) (_g : Iut.SignGroup) : S2267Point S T :=
  S2267QT S N T

theorem S2267smul_eq {T : (Over S)ᵒᵖ} (g : Iut.SignGroup) (P : S2267Point S T) :
    g • P = P ≫ S1971SchemeAut g := rfl

theorem S2267PT_back
    (M : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))
    (T : (Over S)ᵒᵖ) :
    S2267PT S M T =
      ((S2152Q.map (T.unop.hom.op).toLoc).toFunctor.obj M).back := rfl

theorem S2267QT_back
    (N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))
    (T : (Over S)ᵒᵖ) :
    S2267QT S N T =
      ((S2152Q.map (T.unop.hom.op).toLoc).toFunctor.obj N).back := rfl

#print axioms S2267smul_eq
#print axioms S2267PT_back

end LeanFormal.IUT.XiFPaper.S2267QHomEqualizerMulActionActual

end
