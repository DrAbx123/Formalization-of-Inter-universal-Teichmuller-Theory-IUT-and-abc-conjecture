/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual
import tmp.sheaf.xif.paper.Mzk1AxiomGateActual
import Mathlib.Tactic

/-! # Mzk1HqnegCleanGateQpilotActual — hqneg clean gate (A601, qpilot lane)

The `hqneg` hypothesis (`requirementSignedQ (requirementOfReading T R) < 0`) is
only a hypothesis in the final assembly; this gate checks that the assembly
theorems do not pick up `sorryAx` and are usable with an explicit `hqneg`
hypothesis.  Machine output via `#print axioms`. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HqnegCleanGateQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual

/-! ### Axiom gate over the assembly with `hqneg` as a hypothesis -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual.cor312Conclusion_final
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual.no_defeq_vacuity
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual.target_matches_paper

/-- With an explicit `hqneg` hypothesis the assembly's Cor 3.12 conclusion holds
(no sorry, no axiom beyond the allowed ones). -/
theorem hqneg_gate_cor312
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (R : PaperKummerReading T)
    (hqneg : requirementSignedQ (requirementOfReading T R) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (cor312Contract_final T R hqneg ipl hipl she hshe apt hapt) :=
  cor312Conclusion_final T R hqneg ipl hipl she hshe apt hapt

#check hqneg_gate_cor312

end LeanFormal.IUT.XiFPaper.Mzk1HqnegCleanGateQpilotActual
end
