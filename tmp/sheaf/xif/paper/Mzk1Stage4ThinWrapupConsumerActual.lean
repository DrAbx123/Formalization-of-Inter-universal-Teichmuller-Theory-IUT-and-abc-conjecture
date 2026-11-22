import tmp.sheaf.xif.paper.Mzk1Stage4A618AuditProofActual
import tmp.sheaf.xif.paper.Mzk1Stage4GapStructuralConsumerActual

/-! # Mzk1Stage4ThinWrapupConsumerActual (stage4 lane; thin wrap-up)

A648 module: thin wrap-up consumers over the green audit-proof and gap-structural
chains (no new declarations of mathematical content).  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4ThinWrapupConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4A618AuditProofActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4GapStructuralConsumerActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open scoped BigOperators

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Thin wrap-up 1: the audit target-match gate. -/
theorem thin_target_matches (R : PaperKummerReading T) :
    requirementSignedTheta (requirementOfReading T R) = R.thetaReading :=
  audit_target_matches T R

/-- Thin wrap-up 2: the no-defeq-vacuity gate. -/
theorem thin_no_defeq (R : PaperKummerReading T) :
    requirementSignedQ (requirementOfReading T R) = R.qReading :=
  audit_no_defeq_vacuity T R

/-- Thin wrap-up 3: the gap structural height bound. -/
theorem thin_gap_height :
    Mzk1Stage4HeightEstimateActual.height11 <=
      (1 + 1 / 10 : Real) * Real.log 11 + (11 + 0) :=
  gapStructuralConsumer_height

#print axioms thin_target_matches
#print axioms thin_no_defeq
#print axioms thin_gap_height

#check thin_target_matches
#check thin_no_defeq
#check thin_gap_height

end LeanFormal.IUT.XiFPaper.Mzk1Stage4ThinWrapupConsumerActual
end
