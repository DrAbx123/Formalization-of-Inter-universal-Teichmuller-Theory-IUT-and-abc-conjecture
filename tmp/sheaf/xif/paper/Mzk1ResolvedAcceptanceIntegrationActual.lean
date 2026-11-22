/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ResolvedAcceptanceActual
import tmp.sheaf.xif.paper.Mzk1ScalingStrictChainActual
import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual
import Mathlib.Tactic

/-! # Mzk1ResolvedAcceptanceIntegrationActual — resolved acceptance into the final assembly

A561: integration of the resolved (R/p positive region) acceptance with the
green final assembly: the final Cor312Conclusion available together with the
resolved region geometry/measure facts, and one bundle carrying both.
 -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ResolvedAcceptanceIntegrationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictRPInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1ResolvedAcceptanceActual
open LeanFormal.IUT.XiFPaper.Mzk1ScalingStrictChainActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- Final Cor 3.12 conclusion from a genuine realization (re-export). -/
theorem finalAssembly_cor312_resolved
    (D : KummerXiERealization T)
    (hqneg : requirementSignedQ (xiERequirementOfGenuine T D) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (xiERequirementOfGenuine T D) hqneg
        ipl hipl she hshe apt hapt) :=
  cor312Conclusion_final T D hqneg ipl she apt hipl hshe hapt

/-- The integrated acceptance bundle. -/
structure ResolvedAcceptanceBundle where
  region_subset_hull : qRegionRP T ⊆ s1902Hull T
  region_measure_pos : 0 < rootExtensionProductHaar T (qRegionRP T)
  region_measure_lt_top : rootExtensionProductHaar T (qRegionRP T) < ⊤
  strictMeasureInhabited : Nonempty (KummerXiERealization T)
  paperTargetMatch : PaperTargetStatement C3 P ↔
    ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤ ∧
      qPilotLogVolumeReading P ≤ 0 ∧
      qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3)

/-- The constructed integrated bundle. -/
noncomputable def resolvedAcceptanceBundle : ResolvedAcceptanceBundle T C3 P where
  region_subset_hull := qRegionRP_subset_hull T
  region_measure_pos := qRegionRP_measure_pos T
  region_measure_lt_top := qRegionRP_measure_lt_top T
  strictMeasureInhabited := ⟨strictMeasureRealization T⟩
  paperTargetMatch := target_matches_paper C3 P

#check finalAssembly_cor312_resolved
#check resolvedAcceptanceBundle

end LeanFormal.IUT.XiFPaper.Mzk1ResolvedAcceptanceIntegrationActual
end
