/- ABC bridge radical record: G1 paper radical equals the project radical, and
the criterion statements are equivalent. -/
import tmp.sheaf.xif.paper.Mzk1ABCStatementBridgeActual
import tmp.sheaf.xif.paper.ABCStatementBridgeActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.ABCBridgeRadicalDone
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.Mzk1ABCStatementBridgeActual
open LeanFormal.IUT.XiFPaper.ABCStatementBridgeActual

theorem radical_eq_done (n : Nat) : Mzk1G1Actual.radical n = LeanFormal.IUT.radical n :=
  Mzk1ABCStatementBridgeActual.radical_eq n
theorem abcEquiv_done : ABCStatement ↔ ABCConjecture :=
  ABCStatementBridgeActual.abcStatement_iff_ABCConjecture
#print axioms radical_eq_done
#print axioms abcEquiv_done
end LeanFormal.IUT.XiFPaper.ABCBridgeRadicalDone
end
