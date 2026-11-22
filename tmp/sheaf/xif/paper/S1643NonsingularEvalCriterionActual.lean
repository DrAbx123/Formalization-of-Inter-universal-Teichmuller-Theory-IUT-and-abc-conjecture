import tmp.sheaf.xif.paper.S1626AddXYZSmulEvalPortActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S1643NonsingularEvalCriterionActual
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
open LeanFormal.IUT.XiFPaper.S1626AddXYZSmulEvalPortActual

#check s1626Nonsingular_smulField
#check s1626CurveRing_map
#check s1626AlgebraMap_comp_smulRing
#check s1626SmulEval
#check s1626RingEval_comp_smulRing
#check Jacobian.map_nonsingular
#check Jacobian.equiv_iff_eq_of_Z_eq
#check s1626RingEval

/-- Exact ring-level target. -/
def S1643Nonsingular_smulRing (n : Int) : Prop :=
  (s1626CurveRing.toJacobian).Nonsingular (smulRing n)

/-- Exact evaluated target (type fixed by #check). -/
def S1643Nonsingular_smulEval : Prop :=
  forall (n : Int) {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (eqn : W.toAffine.Equation x y),
    W.toJacobian.Nonsingular (s1626SmulEval W x y n)

end LeanFormal.IUT.XiFPaper.S1643NonsingularEvalCriterionActual
end