import tmp.sheaf.xif.paper.Mzk1Stage4HqnegCleanGateActual

/-! # Mzk1Stage4HqnegConditionalReductionActual (stage4 lane; unique filename)

A602 module: conditional reduction of the hqneg clean gate — with `hqneg` as an explicit
hypothesis, the accepted contract carries the negative q-pilot slot, the comparison, and
the target slot identity.  No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4HqnegConditionalReductionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
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

/-- Conditional reduction: the accepted contract has negative q-pilot slot. -/
theorem hqneg_contract_q_negative (D : KummerXiERealization T)
    (hqneg : HqnegHypothesis T D)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    (acceptedBundle T D hqneg ipl hipl apt hapt).contract.qSigned < 0 :=
  (acceptedBundle T D hqneg ipl hipl apt hapt).contract.q_negative

/-- Conditional reduction: the accepted contract has the signed comparison. -/
theorem hqneg_contract_comparison (D : KummerXiERealization T)
    (hqneg : HqnegHypothesis T D)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    (acceptedBundle T D hqneg ipl hipl apt hapt).contract.qSigned ≤ (acceptedBundle T D hqneg ipl hipl apt hapt).contract.thetaSigned :=
  le_trans (acceptedBundle T D hqneg ipl hipl apt hapt).contract.q_le_target
    (acceptedBundle T D hqneg ipl hipl apt hapt).contract.target_le_theta

#check hqneg_contract_q_negative
#check hqneg_contract_comparison

end LeanFormal.IUT.XiFPaper.Mzk1Stage4HqnegConditionalReductionActual
end
