import tmp.sheaf.xif.paper.S2937AbsNormJLeQPilotActual
import tmp.sheaf.xif.paper.S2936ThetaUpperConstantActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2933PerTripleThetaCertificateActual
open LeanFormal.IUT.XiFPaper.S2921HeightBridgeActual
open LeanFormal.IUT.XiFPaper.S2936ThetaUpperConstantActual
open LeanFormal.IUT.XiFPaper.S2937AbsNormJLeQPilotActual
open LeanFormal.IUT.XiFPaper.S2792NormalizedLineBundleBridge
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2944ThetaLinkRealization

/-- AJ for the realized S2936 absorption. -/
noncomputable abbrev S2944AJ (n : Nat) : Real := S2936AJ n

/-- epsilon for the realized S2936 absorption. -/
noncomputable abbrev S2944Eps (n : Nat) (l : Nat) : Real := S2936Eps n l

/-- Theta upper bound in region form, using S2937's actual S≤Q. -/
theorem S2944_theta_le_region
    (n : Nat) (hn : 2 <= n)
    (a b c : Nat) (habc : IsABCTriple a b c) :
    S2933ThetaUpper n a b c <=
      6 * (1 + S2944Eps n S2771FiveLabel.value) *
          S2792RegionVolume a b c +
        S2944AJ n := by
  exact S2936_thetaUpper_constant_bound n hn
    (fun a b c h => S2937_S2921S_le_S2921Q a b c h) a b c habc

/-- Theta link realization: S2936's constant absorption fed by S2937's
actual S ≤ Q comparison. -/
theorem S2944ThetaLinkRealization
    (n : Nat) (hn : 2 <= n)
    (a b c : Nat) (habc : IsABCTriple a b c) :
    S2933ThetaUpper n a b c <=
      6 * (1 + S2936Eps n S2771FiveLabel.value) *
          S2792RegionVolume a b c +
        S2936AJ n :=
  S2944_theta_le_region n hn a b c habc

#check S2944AJ
#check S2944Eps
#check S2944_theta_le_region
#check S2944ThetaLinkRealization
#print axioms S2944_theta_le_region
#print axioms S2944ThetaLinkRealization

end LeanFormal.IUT.XiFPaper.S2944ThetaLinkRealization
end
