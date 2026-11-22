import tmp.sheaf.xif.paper.Mzk1Stage4FinalAcceptanceSelfcheckActual
import tmp.sheaf.xif.paper.Mzk1Stage4ABCStage5InputActual
import tmp.sheaf.xif.paper.Mzk1CThetaConsumerIndependentActual

/-! # Mzk1Stage4AcceptanceWrapupActual (stage4 lane; unique filename)

A572 module: stage4-lane acceptance wrap-up — the resolved Cor 3.12 output, the
constant form, the ABC Stage 5 input, and the numeric C_Theta, gathered from
green/stage4-owned files.  No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4AcceptanceWrapupActual

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
open LeanFormal.IUT.XiFPaper.Mzk1ResolvedABCStage5Actual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4FinalAcceptanceSelfcheckActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCStage5InputActual
open LeanFormal.IUT.XiFPaper.Mzk1CThetaConsumerIndependentActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312NumericalContentActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open scoped BigOperators

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Wrap-up 1: the accepted bundle's Cor 3.12 conclusion. -/
theorem wrapup_cor312 (D : KummerXiERealization T)
    (hqneg : Real.log (D.vol {qPilotInThetaCarrier T}) < 0)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    Cor312Conclusion (acceptedBundle T D hqneg ipl hipl apt hapt).contract :=
  selfcheck_cor312 T D hqneg ipl hipl apt hapt

/-- Wrap-up 2: the accepted bundle supplies the ABC Stage 5 input. -/
theorem wrapup_stage5 (D : KummerXiERealization T)
    (hqneg : Real.log (D.vol {qPilotInThetaCarrier T}) < 0)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    ABCStage5Input :=
  selfcheck_stage5 T D hqneg ipl hipl apt hapt

/-- Wrap-up 3: numeric C_Theta >= -1 for the Unit X instance. -/
theorem wrapup_numeric_cTheta (L : Real) (hL : 0 < L) :
    -1 <= numericCTheta L :=
  numericCTheta_ge_neg_one L hL

/-- Wrap-up 4: numeric Stage 5 input for the Unit X instance. -/
theorem wrapup_numeric_stage5 (L : Real) (hL : 0 < L) : ABCStage5Input :=
  Mzk1Stage4ABCStage5InputActual.numeric_stage5 L hL

#check wrapup_cor312
#check wrapup_stage5
#check wrapup_numeric_cTheta
#check wrapup_numeric_stage5

end LeanFormal.IUT.XiFPaper.Mzk1Stage4AcceptanceWrapupActual
end
