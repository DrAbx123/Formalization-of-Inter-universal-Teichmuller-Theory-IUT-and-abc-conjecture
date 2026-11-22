/- P6 wiring chain: weighted IV inequality + paper bound + display assembly
packaged as separate actual consequences (route-valid P5/P6 inputs). -/
import tmp.sheaf.xif.paper.Mzk1P6IVInequalityActual
import tmp.sheaf.xif.paper.Mzk1P6PaperBoundActual
import tmp.sheaf.xif.paper.Mzk1P6IVDisplayAssemblyActual
import tmp.sheaf.xif.paper.Mzk1P6Thm110DisplayActual
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P6IVPaperBoundWiringChainActual
open LeanFormal.IUT
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open LeanFormal.IUT.XiFPaper.Mzk1P6IVActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PaperBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1P6IVInequalityActual
open LeanFormal.IUT.XiFPaper.Mzk1P6IVDisplayAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1P6Thm110DisplayActual
theorem p6Wiring_ivWeighted (n : Nat) (hn : 2 ≤ n) (D Q S T : Real)
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hT : 0 ≤ T) (l : Real)
    (hl : l = 2 * (n : Real) + 1) :
    p6IVR n D Q S T ≤ (l + 5) / 4 * p6IVD l D - (l + 1) / 24 * p6IVQ l Q +
      p6IVS l S + (l + 5) * p6IVT l T :=
  p6_iv_weighted_inequality n hn D Q S T hD hS hT l hl
theorem p6Wiring_paper (n : Nat) (hn : 1 ≤ n) (D Q S T : Real) :
    p6IVR n D Q S T = p6PaperBound n D Q S T :=
  p6IVR_eq_paperBound n hn D Q S T
#print axioms p6Wiring_ivWeighted
#print axioms p6Wiring_paper
end LeanFormal.IUT.XiFPaper.Mzk1P6IVPaperBoundWiringChainActual
end
