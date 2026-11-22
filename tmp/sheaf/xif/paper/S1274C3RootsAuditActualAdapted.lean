import tmp.sheaf.xif.paper.ConcreteC3RootCompletionActual

/-! # S1274: C3 roots / kummerClass actual audit

Read-only.  The concrete q_v/root donor gives actual roots and root-change in
the algebraic closure of the completion (`ConcreteC3RootCompletionActual`), but
C3's `SourcePilotRegionData.roots` / `kummerClass` live in the completion
itself.  No transport from algebraic closure roots to completion roots exists,
so the C3 fields are not constructed; the exact obstruction is recorded below.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1274C3RootsAuditActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.ConcreteC3RootCompletionActual

#check ConcreteC3RootCompletionActual
#check concreteC3RootCompletionActual
#check ConcreteC3RootCompletionActual.usableRoots
#check ConcreteC3RootCompletionActual.usableRootsPrime
#check ConcreteC3RootCompletionActual.usableRootChange
#check ConcreteC3RootCompletionActual.usableRootChange_eq_diff
#check completionRootSystemObstruction
#check completionRootSystemObstruction_iff
#check tensorLandingObstruction

end LeanFormal.IUT.XiFPaper.S1274C3RootsAuditActualAdapted
end
