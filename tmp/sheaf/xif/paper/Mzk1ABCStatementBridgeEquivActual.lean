/- Re-export the actual ABCStatement <-> ABCConjecture equivalence. -/
import tmp.sheaf.xif.paper.ABCStatementBridgeActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ABCStatementBridgeEquivActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.ABCStatementBridgeActual
theorem abcStatement_iff_ABCConjectureDone : ABCStatement ↔ ABCConjecture :=
  ABCStatementBridgeActual.abcStatement_iff_ABCConjecture
theorem abcStatement_implies_ABCConjectureDone (h : ABCStatement) : ABCConjecture :=
  ABCStatementBridgeActual.abcStatement_to_ABCConjecture h
#print axioms abcStatement_iff_ABCConjectureDone
end LeanFormal.IUT.XiFPaper.Mzk1ABCStatementBridgeEquivActual
end
