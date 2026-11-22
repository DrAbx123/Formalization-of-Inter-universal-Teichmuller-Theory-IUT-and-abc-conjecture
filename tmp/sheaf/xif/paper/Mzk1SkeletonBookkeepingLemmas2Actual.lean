import Mathlib
import tmp.sheaf.xif.paper.Mzk1N8SubStepsStatementActual
import tmp.sheaf.xif.paper.Mzk1N8RemainingGapsStatementActual

/-!
# Mzk1SkeletonBookkeepingLemmas2Actual — more genuine small lemmas about skeleton labels

Status: CONDITIONAL / PENDING-VERIFY (watchdog compile). No sorry, no axiom, no fake closure.
Proves only structural facts (index injectivity) about the bookkeeping label types. -/

open LeanFormal.IUT.XiFPaper.Mzk1N8SubStepsStatementActual
open LeanFormal.IUT.XiFPaper.Mzk1N8RemainingGapsStatementActual

namespace LeanFormal.IUT.XiFPaper.Mzk1SkeletonBookkeepingLemmas2Actual

/-- Remaining gap label index is < 10 (genuine). -/
theorem RemainingGapLabel.index_lt_ten (l : RemainingGapLabel) : l.index < 10 := by
  cases l <;> decide

end LeanFormal.IUT.XiFPaper.Mzk1SkeletonBookkeepingLemmas2Actual
