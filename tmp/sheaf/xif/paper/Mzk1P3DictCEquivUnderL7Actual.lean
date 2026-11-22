import tmp.sheaf.xif.paper.Mzk1P3DictCBoxFromL6Actual
import tmp.sheaf.xif.paper.Mzk1P3DictCReverseL7Actual
import Mathlib.Tactic

/-! # CONDITIONAL: box <=> L6 under L7 + side conditions -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictCEquivUnderL7Actual

open LeanFormal.IUT.XiFPaper.Mzk1P3DictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperStepVBoxActual
open LeanFormal.IUT.XiFPaper.Mzk1DExactLowerActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaDataLegalityActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictCBoxFromL6Actual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictCReverseL7Actual

/-- Conditional DICT-C equivalence: with D=D_exact, L7, Mestre-Oesterle,
ThetaDataLegality, logp>=0, l>=5, S>=0, T>=0:
boxSlack >= 0 <=> L6. -/
theorem boxSlack_iff_L6_of_L7
    (hMO : MestreOesterleBound) (C : PrimeConductorCurve)
    (l : Nat) (L : ThetaDataLegality C l) (D D_exact Q S Tstar : Real)
    (hD : D = D_exact)
    (hL7 : DExactLowerTarget C (l : Real) D_exact)
    (hlogp : 0 <= Real.log (C.p : Real))
    (hl : 5 <= (l : Real)) (hS : 0 <= S) (hT : 0 <= Tstar) :
    0 <= boxSlack (l : Real) D Q S Tstar <->
      L6ReducedInequality C (l : Real) D := by
  constructor
  · intro hbox
    rw [hD]
    exact l6Reduced_of_dExactLower hMO C l L D_exact hL7 hlogp
  · intro hL6
    exact boxSlack_nonneg_of_L6 C (l : Real) D Q S Tstar hl hS hT hL6

#check boxSlack_iff_L6_of_L7
end LeanFormal.IUT.XiFPaper.Mzk1P3DictCEquivUnderL7Actual
end
