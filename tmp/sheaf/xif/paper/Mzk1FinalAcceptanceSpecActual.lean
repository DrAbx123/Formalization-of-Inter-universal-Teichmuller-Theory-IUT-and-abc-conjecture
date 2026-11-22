/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual
import tmp.sheaf.xif.paper.Mzk1PaperTargetMatchingActual
import tmp.sheaf.xif.paper.Mzk1StrictMeasureInstantiationActual
import Mathlib.Tactic
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import tmp.sheaf.n8.closure.SourcePilotRegion
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual

/-! # Mzk1FinalAcceptanceSpecActual — final acceptance specification object

A565: a single specification object with the three acceptance payloads as
function-valued fields (final Cor312Conclusion, paper target match, strict-measure
realization inhabitant), constructed from the green components. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1FinalAcceptanceSpecActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperTargetMatchingActual
open LeanFormal.IUT.XiFPaper.Mzk1StrictMeasureInstantiationActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- The final acceptance specification. -/
structure FinalAcceptanceSpec where
  /-- final Cor 3.12 payload from the assembly. -/
  cor312Payload : ∀ (D : KummerXiERealization T)
    (hqneg : requirementSignedQ (xiERequirementOfGenuine T D) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt),
    Cor312Conclusion (requirementContract (xiERequirementOfGenuine T D) hqneg
      ipl hipl she hshe apt hapt)
  /-- paper target match payload. -/
  paperTargetPayload : PaperTargetStatement C3 P ↔
    ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤ ∧
      qPilotLogVolumeReading P ≤ 0 ∧
      qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3)
  /-- strict-measure realization payload. -/
  strictMeasurePayload : Nonempty (KummerXiERealization T)

/-- The constructed final acceptance specification (all fields proved). -/
noncomputable def finalAcceptanceSpec : FinalAcceptanceSpec T C3 P where
  cor312Payload := by
    intro D hqneg ipl hipl she hshe apt hapt
    exact cor312Conclusion_final T D hqneg ipl she apt hipl hshe hapt
  paperTargetPayload := target_matches_paper C3 P
  strictMeasurePayload := ⟨strictMeasureRealization T⟩

#check finalAcceptanceSpec

end LeanFormal.IUT.XiFPaper.Mzk1FinalAcceptanceSpecActual
end
