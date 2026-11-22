import tmp.sheaf.xif.paper.S2798StableEverywhere37Actual
import tmp.sheaf.xif.paper.S2797ClauseA37ConditionalActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2786SignQuotientActual
open LeanFormal.IUT.XiFPaper.S2797ClauseA37ConditionalActual
open LeanFormal.IUT.XiFPaper.S2798StableEverywhere37Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2813ClauseA37ReadyActual

/-- ClauseA for E37/Q(i), conditional only on the sign-quotient record S:
stable reduction everywhere is the actual S2798 theorem. -/
noncomputable def S2813ClauseA
    (S : SourceSignQuotientData S2786Arithmetic) :
    SourceClauseA S2786Arithmetic S :=
  S2797ClauseA S S2798_hasStableReductionEverywhere

#check S2813ClauseA
#print axioms S2813ClauseA

end LeanFormal.IUT.XiFPaper.S2813ClauseA37ReadyActual
end
