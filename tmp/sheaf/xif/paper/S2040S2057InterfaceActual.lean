import tmp.sheaf.xif.paper.S2040S2060Actual
import tmp.sheaf.xif.paper.S2057RootStackThetaPilotActual
import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual

/-! # S2040 / S2057 root-stack interface

Records the actual finite root-stack Θ-pilot object from S2057 and the exact
missing paper O^tri/q_v/O^×μ attachment.  The earlier
`S2040RootStackThetaPilotActual.S2040RootStackThetaPilotObject` is the
algebraic-closure LGP model and is **not** used here as the paper finite
root-stack carrier. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2040S2057InterfaceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S2057RootStackThetaPilotActual
open LeanFormal.IUT.XiFPaper.S2040S2060Actual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S798OtRootStackSectionActual
open LeanFormal.IUT.XiFPaper.S201RootThetaNormLActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual finite root-stack Θ-pilot object of S2057 (q[2u], theta values,
root hodgeTwoLthRoot). -/
noncomputable def s2040S2057ThetaPilotObject :
    S2057RootStackThetaPilotObject (l := l) T b :=
  s2057RootStackThetaPilotObject T b

theorem s2040S2057ThetaPilotObject_pow :
    (s2040S2057ThetaPilotObject T b).root ^ (2 * l.value) =
      (s2040S2057ThetaPilotObject T b).qSection := 
  (s2040S2057ThetaPilotObject T b).root_pow

theorem s2040S2057ThetaPilotObject_theta (j : SignedLabel l.value) :
    (s2040S2057ThetaPilotObject T b).thetaValue j =
      stackRootSection T b ^ (gaussExponent j.1).toNat :=
  (s2040S2057ThetaPilotObject T b).thetaValue_eq j

/-- Exact missing paper O^tri root-stack carrier data: the paper O^tri(T_X)
carrier, its q_v, and the O^×μ attachment, distinct from the finite root-stack
model and from the repo qVFamily (S342 no-go).  No inhabitant is asserted. -/
structure S2040PaperOtriAttachmentRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  Otri : Type
  qv : Otri
  OUnits : Type
  OUnitsMu : Type
  qv_root_attachment : Prop
  OUnitsMu_attachment : Prop
  norm_law : Prop

#check s2040S2057ThetaPilotObject
#check s2040S2057ThetaPilotObject_pow
#check s2040S2057ThetaPilotObject_theta
#check S2040PaperOtriAttachmentRequired

end LeanFormal.IUT.XiFPaper.S2040S2057InterfaceActual
end
