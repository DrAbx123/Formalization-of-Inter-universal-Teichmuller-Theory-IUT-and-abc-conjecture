import tmp.sheaf.xif.paper.Mzk1AcceptanceResolvedActual
import tmp.sheaf.xif.paper.Mzk1AcceptanceIntegrationActual
import tmp.sheaf.xif.paper.Mzk1ResolvedABCStage5Actual

/-! # Mzk1Stage4FinalAcceptanceSelfcheckActual (stage4 lane; unique filename)

A570 module: stage4-lane acceptance self-checks on the RESOLVED assembly, using only
stage4-owned or green files (no owner-exclusive file is modified).  Records: canonical
reading discharge, Cor 3.12 conclusion, ABC Stage 5 input, and the constant form.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4FinalAcceptanceSelfcheckActual

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
open LeanFormal.IUT.XiFPaper.Mzk1AcceptanceResolvedActual
open LeanFormal.IUT.XiFPaper.Mzk1AcceptanceIntegrationActual
open LeanFormal.IUT.XiFPaper.Mzk1ResolvedABCStage5Actual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open scoped BigOperators

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Self-check 1: the named input is discharged (rfl at canonical reading). -/
theorem selfcheck_named_input_resolved (D : KummerXiERealization T) :
    (canonicalReading T D).qReading_log = rfl ∧
      (canonicalReading T D).thetaReading_log = rfl :=
  canonical_named_input_discharged T D

/-- Self-check 2: the accepted bundle gives the Cor 3.12 conclusion. -/
theorem selfcheck_cor312 (D : KummerXiERealization T)
    (hqneg : Real.log (D.vol {qPilotInThetaCarrier T}) < 0)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    Cor312Conclusion (acceptedBundle T D hqneg ipl hipl apt hapt).contract :=
  accepted_cor312 T D hqneg ipl hipl apt hapt

/-- Self-check 3: the resolved acceptance supplies the ABC Stage 5 input. -/
theorem selfcheck_stage5 (D : KummerXiERealization T)
    (hqneg : Real.log (D.vol {qPilotInThetaCarrier T}) < 0)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    ABCStage5Input :=
  acceptedBundle_stage5 T D hqneg ipl hipl apt hapt

/-- Self-check 4: the contract slots realize the canonical readings. -/
theorem selfcheck_contract_slots (D : KummerXiERealization T)
    (hqneg : Real.log (D.vol {qPilotInThetaCarrier T}) < 0)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    (acceptedBundle T D hqneg ipl hipl apt hapt).contract.qSigned =
        (canonicalReading T D).qReading ∧
      (acceptedBundle T D hqneg ipl hipl apt hapt).contract.thetaSigned =
        (canonicalReading T D).thetaReading :=
  acceptedBundle_stage5_contract T D hqneg ipl hipl apt hapt

#check selfcheck_named_input_resolved
#check selfcheck_cor312
#check selfcheck_stage5
#check selfcheck_contract_slots

end LeanFormal.IUT.XiFPaper.Mzk1Stage4FinalAcceptanceSelfcheckActual
end
