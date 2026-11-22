import tmp.sheaf.xif.paper.S2434D9AttackActual
import tmp.sheaf.xif.paper.S2425NatIsoCastHelpersActual
import tmp.sheaf.xif.paper.S2134D9DescentActual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2434D9AttackActual
open LeanFormal.IUT.XiFPaper.S2425NatIsoCastHelpersActual
open LeanFormal.IUT.XiFPaper.S2134D9DescentActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2435D9GateActual

-- Gate checks only; actual declarations are in S2434/S2425/S2134.
#check S2434SlicePush_iff_pullHom
#check S2434D9Missing_iff_three
#check @natIsoOfPointwiseEqToIso
#check @hasEffectiveDescentPresieve_top
#check @S2134EffDescent_identityCover

end LeanFormal.IUT.XiFPaper.S2435D9GateActual

end
