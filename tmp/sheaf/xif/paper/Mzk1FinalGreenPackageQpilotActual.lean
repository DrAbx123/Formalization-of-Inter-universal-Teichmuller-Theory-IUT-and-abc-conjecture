/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1StrictnessPackageQpilotActual
import tmp.sheaf.xif.paper.Mzk1WrapUpCompletionQpilotActual
import tmp.sheaf.xif.paper.Mzk1EvidenceBundleGreenActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1Cor312FinalStatementActual

/-! # Mzk1FinalGreenPackageQpilotActual — final green package (qpilot lane)

A589: one package over green components: strictness package, wrap-up completion
summary, and the green evidence bundle. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1FinalGreenPackageQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1FinalWrapUpPackageActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalStatementActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1StrictnessPackageQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1WrapUpCompletionQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1EvidenceBundleGreenActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The final green package. -/
structure FinalGreenPackage where
  strictness : StrictnessPackage
  gateRows : wrapUpGateRows.length = 8
  paperTargetIff : ∀ qMag thetaMag : Real,
    paperTarget qMag thetaMag ↔ thetaMag ≤ qMag
  evidence : Nonempty (EvidenceBundle T)

/-- The constructed final green package. -/
noncomputable def finalGreenPackage : FinalGreenPackage T where
  strictness := strictnessPackage
  gateRows := completion_gateRows
  paperTargetIff := completion_paperTarget
  evidence := ⟨evidenceBundle T⟩

#check finalGreenPackage

end LeanFormal.IUT.XiFPaper.Mzk1FinalGreenPackageQpilotActual
end
