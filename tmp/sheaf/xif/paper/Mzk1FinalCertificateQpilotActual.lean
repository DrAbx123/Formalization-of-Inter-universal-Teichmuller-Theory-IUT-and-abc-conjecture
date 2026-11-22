/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1FinalWrapUpPackageActual
import tmp.sheaf.xif.paper.Mzk1StrictnessPackageQpilotActual
import tmp.sheaf.xif.paper.Mzk1EvidenceBundleGreenActual
import tmp.sheaf.xif.paper.Mzk1Gap1NumericWitnessQpilotActual
import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual
import tmp.sheaf.xif.paper.Mzk1Cor312FinalStatementActual

/-! # Mzk1FinalCertificateQpilotActual — final certificate (A593, qpilot lane)

One certificate object over green components: the 8-row Stage-5 gate table,
the paper target equivalence, the 1D/product strictness package, the final
Cor 3.12 conclusion payload, and the Gap-1 numeric witness. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1FinalCertificateQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalStatementActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalWrapUpPackageActual
open LeanFormal.IUT.XiFPaper.Mzk1StrictnessPackageQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1EvidenceBundleGreenActual
open LeanFormal.IUT.XiFPaper.Mzk1Gap1NumericWitnessQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The final certificate. -/
structure FinalCertificate where
  gateRows : wrapUpGateRows.length = 8
  paperTargetIff : ∀ qMag thetaMag : Real,
    paperTarget qMag thetaMag ↔ thetaMag ≤ qMag
  strictness : StrictnessPackage
  cor312Payload : ∀ (R : PaperKummerReading T)
    (hqneg : requirementSignedQ (requirementOfReading T R) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt),
    Cor312Conclusion (cor312Contract_final T R hqneg ipl hipl she hshe apt hapt)
  gap1Witness : ∃ (height volume epsilon : Real), 0 < epsilon ∧
    height ≤ (1 + epsilon) * volume

/-- The constructed final certificate (all fields proved). -/
noncomputable def finalCertificate : FinalCertificate T where
  gateRows := wrapUpGateRows_length
  paperTargetIff := wrapUp_paperTarget
  strictness := strictnessPackage
  cor312Payload := by
    intro R hqneg ipl hipl she hshe apt hapt
    exact cor312Conclusion_final T R hqneg ipl hipl she hshe apt hapt
  gap1Witness := gap1_numeric_witness

#check finalCertificate

end LeanFormal.IUT.XiFPaper.Mzk1FinalCertificateQpilotActual
end
