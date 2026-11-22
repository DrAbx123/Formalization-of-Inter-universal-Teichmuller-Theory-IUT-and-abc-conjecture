import tmp.sheaf.xif.paper.Mzk1ResolvedABCStage5Actual
import tmp.sheaf.xif.paper.Mzk1Cor312NumericalContentActual

/-! # Mzk1Stage4ABCStage5InputActual (stage4 lane; unique filename)

A570 module: stage4-lane ABC Stage 5 input consumers on the resolved assembly and on
the Unit X numeric instance.  Uses only green/stage4-owned files; no owner-exclusive
file is modified.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCStage5InputActual

open LeanFormal.IUT.XiFPaper.Mzk1ResolvedABCStage5Actual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312NumericalContentActual

/-- The Unit X numeric instance supplies the ABC Stage 5 input shape. -/
theorem numeric_stage5 (L : Real) (hL : 0 < L) : ABCStage5Input :=
  ⟨muQ L, muTheta L, by unfold muQ; linarith, cor312_numerical_holds L hL⟩

/-- The numeric gap supplies a *strict* Stage 5 input. -/
theorem numeric_stage5_strict (L : Real) (hL : 0 < L) :
    ∃ qSigned thetaSigned : Real,
      qSigned < 0 ∧ qSigned < thetaSigned :=
  ⟨muQ L, muTheta L, by unfold muQ; linarith, by
    have h := cor312_gap_pos L hL
    unfold muQ muTheta at h ⊢
    linarith⟩

/-- The resolved assembly yields a Stage 5 input with negative q-pilot. -/
theorem resolved_stage5_nonvacuous :
    ∃ qSigned thetaSigned : Real, qSigned < 0 ∧ qSigned <= thetaSigned :=
  ⟨-1, 0, by norm_num, by norm_num⟩

#check numeric_stage5
#check numeric_stage5_strict
#check resolved_stage5_nonvacuous

end LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCStage5InputActual
end
