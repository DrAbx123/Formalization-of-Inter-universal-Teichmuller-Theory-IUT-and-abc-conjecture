/- Re-export the accepted P6 paper-bound and IV-inequality components. -/
import tmp.sheaf.xif.paper.Mzk1P6PaperBoundActual
import tmp.sheaf.xif.paper.Mzk1P6IVActual
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P6PaperBoundReexportDoneActual
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open LeanFormal.IUT.XiFPaper.Mzk1P6IVActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PaperBoundActual
theorem p6PaperBound_ivR_eq (n : Nat) (hn : 1 ≤ n) (D Q S T : Real) :
    p6IVR n D Q S T = p6PaperBound n D Q S T :=
  p6IVR_eq_paperBound n hn D Q S T
theorem p6IV_inequality_done (n : Nat) (hn : 2 ≤ n) (D Q S T : Real)
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hT : 0 ≤ T) (l : Real) (hl : l = 2 * (n : Real) + 1) :
    p6IVR n D Q S T ≤ (l + 5) / 4 * p6IVD l D - (l + 1) / 24 * p6IVQ l Q +
      p6IVS l S + (l + 5) * p6IVT l T :=
  p6_iv_inequality n hn D Q S T hD hS hT l hl
#print axioms p6PaperBound_ivR_eq
#print axioms p6IV_inequality_done
end LeanFormal.IUT.XiFPaper.Mzk1P6PaperBoundReexportDoneActual
end
