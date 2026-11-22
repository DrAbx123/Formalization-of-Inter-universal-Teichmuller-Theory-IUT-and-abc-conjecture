import tmp.sheaf.xif.paper.Mzk1AcceptanceIntegrationActual

/-! # Mzk1ResolvedABCStage5Actual — ABC Stage 5 input from the resolved acceptance

A569 module (no new mathematics): the resolved (canonical-reading) acceptance bundle
supplies the ABC Stage 5 input shape `∃ q θ, q < 0 ∧ q ≤ θ` — the paper's signed
Cor 3.12 output consumed by the explicit-estimate stage.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ResolvedABCStage5Actual

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
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open scoped BigOperators

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The ABC Stage 5 input shape: a negative signed q-pilot value bounded by a signed
Theta-pilot value. -/
def ABCStage5Input : Prop :=
  ∃ qSigned thetaSigned : Real, qSigned < 0 ∧ qSigned <= thetaSigned

/-- The resolved acceptance bundle supplies the ABC Stage 5 input shape. -/
theorem acceptedBundle_stage5 (D : KummerXiERealization T)
    (hqneg : Real.log (D.vol {qPilotInThetaCarrier T}) < 0)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    ABCStage5Input :=
  ⟨(canonicalReading T D).qReading, (canonicalReading T D).thetaReading, hqneg,
    le_of_lt (paperKummerReading_strict T (canonicalReading T D))⟩

/-- The accepted bundle's contract slots realize the ABC Stage 5 input values. -/
theorem acceptedBundle_stage5_contract (D : KummerXiERealization T)
    (hqneg : Real.log (D.vol {qPilotInThetaCarrier T}) < 0)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    (acceptedBundle T D hqneg ipl hipl apt hapt).contract.qSigned =
        (canonicalReading T D).qReading ∧
      (acceptedBundle T D hqneg ipl hipl apt hapt).contract.thetaSigned =
        (canonicalReading T D).thetaReading := by
  constructor
  · unfold acceptedBundle cor312Contract_final requirementContract signedCor312Contract
    exact (no_defeq_vacuity T (canonicalReading T D)).symm
  · unfold acceptedBundle cor312Contract_final requirementContract signedCor312Contract
    exact (target_matches_paper T (canonicalReading T D)).symm

#check ABCStage5Input
#check acceptedBundle_stage5
#check acceptedBundle_stage5_contract

end LeanFormal.IUT.XiFPaper.Mzk1ResolvedABCStage5Actual
end
