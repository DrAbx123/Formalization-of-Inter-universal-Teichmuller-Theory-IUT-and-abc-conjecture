/- Re-export the actual radical identity for the G1/project radical bridge. -/
import tmp.sheaf.xif.paper.Mzk1ABCStatementBridgeActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeRadicalDoneActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.Mzk1ABCStatementBridgeActual
theorem radical_eq_done (n : Nat) : Mzk1G1Actual.radical n = LeanFormal.IUT.radical n :=
  Mzk1ABCStatementBridgeActual.radical_eq n
#print axioms radical_eq_done
end LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeRadicalDoneActual
end
