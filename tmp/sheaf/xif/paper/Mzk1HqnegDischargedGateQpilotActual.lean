/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HqnegHullModelActual
import tmp.sheaf.xif.paper.Mzk1HqnegConditionalReductionQpilotActual
import tmp.sheaf.xif.paper.Mzk1QPilotSHEDoubleImageActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual

/-! # Mzk1HqnegDischargedGateQpilotActual — discharged hqneg acceptance gate

A606 (qpilot lane): consumes the green hull side model (imported only) to get an
unconditional Cor 3.12 contract/conclusion from a negative q reading `qRead < 0`.
Qualitative slots: ipl := SHEArrowStatement T with its green proof; she/apt are
explicit parameters (no True). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HqnegDischargedGateQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1HqnegHullModelActual
open LeanFormal.IUT.XiFPaper.Mzk1HqnegConditionalReductionQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem hqnegDischarged_exists {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (qRead : Real) (hq : qRead < 0)
    (she : Prop) (hshe : she) (apt : Prop) (hapt : apt) :
    ∃ C : StepXIContract, Cor312Conclusion C :=
  hqneg_conditional_exists T (canonicalReading T hq) (canonicalHqneg T hq)
    (SHEArrowStatement T) (sheArrowStatement_proved T) she hshe apt hapt

theorem hqnegDischarged_contract {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (qRead : Real) (hq : qRead < 0)
    (she : Prop) (hshe : she) (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (cor312Contract_final T (canonicalReading T hq) (canonicalHqneg T hq)
        (SHEArrowStatement T) (sheArrowStatement_proved T) she hshe apt hapt) :=
  hqneg_conditional_conclusion T (canonicalReading T hq) (canonicalHqneg T hq)
    (SHEArrowStatement T) (sheArrowStatement_proved T) she hshe apt hapt

#check hqnegDischarged_exists
#check hqnegDischarged_contract

end LeanFormal.IUT.XiFPaper.Mzk1HqnegDischargedGateQpilotActual
end
