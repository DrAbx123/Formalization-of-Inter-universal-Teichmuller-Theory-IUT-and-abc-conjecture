/- P6 paper-bound wiring: the averaged readout equals the paper StepV bound and
is bounded by the normalized procession upper bound. -/
import tmp.sheaf.xif.paper.Mzk1P6PaperBoundActual
import tmp.sheaf.xif.paper.Mzk1P6IVActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P6PaperBoundWiringDoneActual
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open LeanFormal.IUT.XiFPaper.Mzk1P6IVActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PaperBoundActual

theorem p6_wiring_ivR_eq (n : Nat) (hn : 1 ≤ n) (D Q S T : Real) :
    p6IVR n D Q S T = p6PaperBound n D Q S T :=
  p6IVR_eq_paperBound n hn D Q S T

theorem p6_wiring_ivR_le (n : Nat) (hn : 1 ≤ n) (D Q S T : Real) :
    p6IVR n D Q S T ≤ p6PaperBound n D Q S T :=
  p6IVR_le_paperBound n hn D Q S T

theorem p6_wiring_paper_le_upper (n : Nat) (hn : 2 ≤ n) (D Q S T : Real)
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hT : 0 ≤ T) :
    p6PaperBound n D Q S T ≤ ((2 * (n : Real) + 1) + 1) / 4 *
      ((1 + 4 / (2 * (n : Real) + 1)) * D - Q / 6 +
        4 / (2 * (n : Real) + 1) * S + 20 / 3 * T) :=
  p6PaperBound_le_processionUpper n hn D Q S T hD hS hT
#print axioms p6_wiring_ivR_eq
#print axioms p6_wiring_paper_le_upper
end LeanFormal.IUT.XiFPaper.Mzk1P6PaperBoundWiringDoneActual
end
