import tmp.sheaf.xif.paper.S2492CorrectedFSourceBundle
import tmp.sheaf.xif.paper.S2470SignActionActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2492CorrectedFSourceBundle
open LeanFormal.IUT.XiFPaper.S2470SignActionActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2471BundleSignActionActual

/-- The actual sign action of S2470 for the S2492 corrected source bundle. -/
noncomputable def S2471BundleSignAction :
    Iut.OrbicurveSignAction S2492Bundle.xF :=
  S2470SignAction

theorem S2471BundleSignAction_inversion :
    S2471BundleSignAction.inversion = S2492Bundle.ellipticInvolution := rfl

#check S2471BundleSignAction

end LeanFormal.IUT.XiFPaper.S2471BundleSignActionActual
end
