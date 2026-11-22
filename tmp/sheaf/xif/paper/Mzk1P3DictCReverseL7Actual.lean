import tmp.sheaf.xif.paper.Mzk1P3DictionaryActual
import tmp.sheaf.xif.paper.Mzk1DExactLowerActual
import Mathlib.Tactic

/-! # CONDITIONAL: box + DExactLowerTarget + D=D_exact implies L6 -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictCReverseL7Actual

open LeanFormal.IUT.XiFPaper.Mzk1P3DictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperStepVBoxActual
open LeanFormal.IUT.XiFPaper.Mzk1DExactLowerActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaDataLegalityActual

/-- Conditional reverse reduction.  The proof uses L7 only; boxSlack is an
unused explicit hypothesis, showing box>=0 is not the source of L6. -/
theorem L6ReducedInequality_of_DExactLower_and_box
    (hMO : MestreOesterleBound) (C : PrimeConductorCurve)
    (l : Nat) (L : ThetaDataLegality C l) (D D_exact Q S Tstar : Real)
    (hD : D = D_exact)
    (hL7 : DExactLowerTarget C (l : Real) D_exact)
    (hlogp : 0 <= Real.log (C.p : Real))
    (_hbox : 0 <= boxSlack (l : Real) D Q S Tstar) :
    L6ReducedInequality C (l : Real) D := by
  rw [hD]
  exact l6Reduced_of_dExactLower hMO C l L D_exact hL7 hlogp

#check L6ReducedInequality_of_DExactLower_and_box
end LeanFormal.IUT.XiFPaper.Mzk1P3DictCReverseL7Actual
end
