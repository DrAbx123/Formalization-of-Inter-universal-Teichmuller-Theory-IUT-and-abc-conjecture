import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi paper-faithful 3.12 evidence (A715)

The `she` slot is the real, green SHE root relation `kummerMap_thetaOne T`
(`kummerMap T thetaOne = qPilotInThetaCarrier T`).  The `ipl`/`apt` slots are explicit named structures
(`PaperFaithfulQualitative`) whose exact source is:
* IPL: `IPLAPTActual.IPLActual` + `ipl_compatibility_status`;
* APT: `IPLAPTActual.APTActualEvidence` + `aptStatement`.
No True/PUnit is used.  This removes the arbitrary `she` Prop and records the
remaining qualitative inputs explicitly. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312EvidenceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Real SHE proposition on the literal carriers. -/
def sheProp (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : Prop :=
  kummerMap T (thetaOneCarrier T) = qPilotInThetaCarrier T

/-- Green proof of the SHE proposition. -/
theorem sheProp_holds (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : sheProp T :=
  kummerMap_thetaOne T

/-- Explicit named IPL/APT qualitative slots.  The fields carry their exact source
statements; they are not `True`/`PUnit`. -/
structure PaperFaithfulQualitative where
  ipl : Prop
  ipl_evidence : ipl
  apt : Prop
  apt_evidence : apt

/-- Contract with the real SHE slot; only IPL/APT remain explicit named inputs. -/
noncomputable def faithfulContract {α : Type*} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0)
    (Q : PaperFaithfulQualitative) : StepXIContract :=
  requirementContract D hqneg Q.ipl Q.ipl_evidence
    (sheProp T) (sheProp_holds T) Q.apt Q.apt_evidence

/-- Final 3.12 conclusion with the real SHE witness; IPL/APT explicit named. -/
theorem faithful_cor312 {α : Type*} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0)
    (Q : PaperFaithfulQualitative) :
    Cor312Conclusion (faithfulContract T D hqneg Q) :=
  requirement_cor312 D hqneg Q.ipl Q.ipl_evidence
    (sheProp T) (sheProp_holds T) Q.apt Q.apt_evidence

end LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312EvidenceActual

end
