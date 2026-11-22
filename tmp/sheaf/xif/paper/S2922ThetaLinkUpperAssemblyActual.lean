import tmp.sheaf.xif.paper.S2920ThetaLinkHeight
import tmp.sheaf.xif.paper.S2921ThetaLeRegionActual
import tmp.sheaf.xif.paper.S2792NormalizedLineBundleBridge

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2920ThetaLinkHeight
open LeanFormal.IUT.XiFPaper.S2921ThetaLeRegionActual
open LeanFormal.IUT.XiFPaper.S2919ThetaUpperFromProcession
open LeanFormal.IUT.XiFPaper.S2792NormalizedLineBundleBridge
open LeanFormal.IUT.XiFPaper.S2838HeightComparisonReductionActual
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open Finset
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2922ThetaLinkUpperAssembly

/-- The q-pilot / procession comparison as an explicit input. -/
def S2922QPilotProcessionLink (qPilotLog processionAvg : Real) : Prop :=
  qPilotLog ≤ -processionAvg

/-- Assembly data: theta-link height input, procession data, q-pilot link,
and region nonnegativity. -/
structure S2922AssemblyData where
  n : Nat
  hn : 2 ≤ n
  D : Real
  Q : Real
  S : Real
  T : Real
  hD : 0 ≤ D
  hS : 0 ≤ S
  hT : 0 ≤ T
  eps : Real
  heps : 0 ≤ 1 + eps
  height_le_procession :
    S2920HeightLeProcession n D Q S T
  qPilotLog : Real
  processionAvg : Real
  processionAvg_eq :
    processionAvg =
      (1 / (n : Real)) *
        Finset.sum (Finset.Icc 1 n)
          (fun j => collectionBound (2 * (n : Real) + 1) D Q S T j)
  qPilot_link : S2922QPilotProcessionLink qPilotLog processionAvg

/-- Assemble the S2921 certificate from S2922 data. -/
noncomputable def S2922Certificate (A : S2922AssemblyData) :
    ThetaUpperCertificate :=
  S2921Certificate A.n A.hn A.D A.Q A.S A.T A.hD A.hS A.hT A.eps A.heps
    (by
      intro a b c habc
      exact A.height_le_procession a b c habc)

/-- The assembled certificate has the explicit theta upper as AJ. -/
theorem S2922_certificate_AJ (A : S2922AssemblyData) :
    (S2922Certificate A).AJ = S2921ThetaUpper A.n A.D A.Q A.S A.T := rfl

/-- S2922 to the S2919 theta upper bound. -/
theorem S2922_thetaUpper_bound (A : S2922AssemblyData)
    (a b c : Nat) (habc : IsABCTriple a b c) :
    Height.logHeight₁ (abcJInvariant a b c) ≤
      6 * (1 + A.eps) * S2792RegionVolume a b c +
        S2921ThetaUpper A.n A.D A.Q A.S A.T :=
  S2919_thetaUpper_bound (S2922Certificate A) a b c habc

/-- S2922 to the S2838 theta upper gap. -/
theorem S2922_to_S2838ThetaUpperGap (A : S2922AssemblyData) :
    S2838ThetaUpperGap A.eps (S2921ThetaUpper A.n A.D A.Q A.S A.T) :=
  S2919_to_S2838ThetaUpperGap (S2922Certificate A)

/-- The remaining bridge: theta-link algebraic data alone does not imply the
height-to-procession estimate. -/
def S2922ThetaLinkHeightBridge : Prop :=
  ∀ (n : Nat) (D Q S T : Real),
    Nonempty (S2920HeightLeProcession n D Q S T)

/-- Exact first missing lemma: thetaLink data plus qPilot/region gives the
height-to-procession estimate. -/
theorem S2922_from_thetaLink
    (hbridge : S2922ThetaLinkHeightBridge)
    (n : Nat) (D Q S T : Real) : S2920HeightLeProcession n D Q S T :=
  (hbridge n D Q S T).some

#check S2922AssemblyData
#check S2922Certificate
#check S2922_to_S2838ThetaUpperGap
#check S2922_from_thetaLink
#print axioms S2922_to_S2838ThetaUpperGap

end LeanFormal.IUT.XiFPaper.S2922ThetaLinkUpperAssembly
end
