import tmp.sheaf.xif.paper.Mzk1Stage4HqnegCleanGateActual

/-! # Mzk1Stage4HqnegGateConsumerActual (stage4 lane; unique filename)

A602 module: consumers of the hqneg clean gate — the explicit-hypothesis bundle's
contract slots are the canonical readings.  No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4HqnegGateConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1LastNamedResolutionActual
open LeanFormal.IUT.XiFPaper.Mzk1AcceptanceIntegrationActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4HqnegCleanGateActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open scoped BigOperators

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The hqneg bundle's theta slot is the canonical reading. -/
theorem hqneg_bundle_theta (D : KummerXiERealization T)
    (hqneg : HqnegHypothesis T D)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    (acceptedBundle T D hqneg ipl hipl apt hapt).contract.thetaSigned =
      (canonicalReading T D).thetaReading :=
  accepted_target T D hqneg ipl hipl apt hapt

#check hqneg_bundle_theta

end LeanFormal.IUT.XiFPaper.Mzk1Stage4HqnegGateConsumerActual
end
