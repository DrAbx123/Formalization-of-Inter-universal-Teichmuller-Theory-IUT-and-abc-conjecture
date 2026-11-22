import tmp.sheaf.xif.paper.Mzk1P3DictionaryActual
import tmp.sheaf.xif.paper.Mzk1PrimeConductorRouteActual
import Mathlib.Tactic

/-! # GAP: counterexample boxSlack>=0 does NOT imply L6 -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictCCounterexampleActual

open LeanFormal.IUT.XiFPaper.Mzk1P3DictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperStepVBoxActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaDataLegalityActual

/-- Prime-conductor carrier p=2,e=1. -/
def Ctwo : PrimeConductorCurve where
  p := 2
  hp := by norm_num
  e := 1

/-- boxSlack>=0 does not imply L6: l=5,D=S=T=Q=0 gives slack 0 but L6 fails. -/
theorem boxSlack_nonneg_not_implies_L6 :
    exists C : PrimeConductorCurve, exists D Q S Tstar l : Real,
      0 <= boxSlack l D Q S Tstar ∧ ¬ L6ReducedInequality C l D := by
  refine Exists.intro Ctwo (Exists.intro 0 (Exists.intro 0 (Exists.intro 0
    (Exists.intro 0 (Exists.intro 5 ?_)))))
  constructor
  · unfold boxSlack paperLHS paperRHS
    norm_num
  · unfold L6ReducedInequality T
    norm_num [Ctwo]
    have hlog : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
    linarith

#check Ctwo
#check boxSlack_nonneg_not_implies_L6
end LeanFormal.IUT.XiFPaper.Mzk1P3DictCCounterexampleActual
end
