import tmp.sheaf.xif.paper.Mzk1AcceptanceIntegrationActual
import tmp.sheaf.xif.paper.Mzk1Cor312FinalCThetaActual
import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual

/-! # Mzk1Stage4HqnegCleanGateActual (stage4 lane; unique filename)

A601 module: hqneg CLEAN GATE — the negative q-pilot sign enters the final assembly only
as an explicit hypothesis (`hqneg`), never as a hidden axiom: the gate restates the
acceptance with `hqneg` as a parameter and prints the axiom dependencies of the
consuming theorems (expected propext/Classical.choice/Quot.sound, no sorryAx).
No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4HqnegCleanGateActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalCThetaActual
open LeanFormal.IUT.XiFPaper.Mzk1AcceptanceIntegrationActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open scoped BigOperators

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The explicit hqneg hypothesis of the assembly (a real inequality, not an axiom). -/
def HqnegHypothesis (D : KummerXiERealization T) : Prop :=
  Real.log (D.vol {qPilotInThetaCarrier T}) < 0

/-- Clean gate: with `hqneg` as an explicit parameter the accepted bundle gives the
Cor 3.12 conclusion (no hidden sign axiom). -/
theorem clean_gate_cor312 (D : KummerXiERealization T)
    (hqneg : HqnegHypothesis T D)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    Cor312Conclusion (acceptedBundle T D hqneg ipl hipl apt hapt).contract :=
  accepted_cor312 T D hqneg ipl hipl apt hapt

/-- Clean gate: the constant bound also depends on `hqneg` only via an explicit
parameter (the denominator sign). -/
theorem clean_gate_cTheta (R : PaperKummerReading T) (hqneg : R.qReading < 0) :
    -1 <= R.thetaReading / (-R.qReading) :=
  Mzk1Cor312FinalCThetaActual.final_cTheta_ge_neg_one T R hqneg

#print axioms clean_gate_cor312
#print axioms clean_gate_cTheta
#print axioms Mzk1AcceptanceIntegrationActual.accepted_cor312
#print axioms Mzk1Cor312FinalCThetaActual.final_cTheta_ge_neg_one

#check HqnegHypothesis
#check clean_gate_cor312
#check clean_gate_cTheta

end LeanFormal.IUT.XiFPaper.Mzk1Stage4HqnegCleanGateActual
end
