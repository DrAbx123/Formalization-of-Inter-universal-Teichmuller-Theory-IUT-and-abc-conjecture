/- P6 StepV wiring: accept the e-support decomposition and the IV inequality
as one component (two re-exports with independent variable blocks). -/
import tmp.sheaf.xif.paper.Mzk1P6StepVESupportFinalAct
import tmp.sheaf.xif.paper.Mzk1P6StepVAveragesActual
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P6StepVAveragesWiringDoneActual
open LeanFormal.IUT LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open LeanFormal.IUT.XiFPaper.Mzk1P6StepVESupportFinalAct
open LeanFormal.IUT.XiFPaper.Mzk1P6StepVAveragesActual

theorem p6StepV_ivDone (n : Nat) (hn : 2 ≤ n) (D Q S T : Real)
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hT : 0 ≤ T) :
    (1 / (n : Real)) *
        (∑ j ∈ Finset.Icc 1 n, collectionBound (2 * (n : Real) + 1) D Q S T j) ≤
      ((2 * (n : Real) + 1) + 1) / 4 *
        ((1 + 4 / (2 * (n : Real) + 1)) * D - Q / 6 +
          4 / (2 * (n : Real) + 1) * S + 20 / 3 * T) :=
  p6_stepVAverages_ivInequality n hn D Q S T hD hS hT

#print axioms p6StepV_ivDone
end LeanFormal.IUT.XiFPaper.Mzk1P6StepVAveragesWiringDoneActual
end
