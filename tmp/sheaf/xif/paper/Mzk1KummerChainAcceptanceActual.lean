/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import tmp.sheaf.xif.paper.Mzk1KummerRealizationActual
import tmp.sheaf.xif.paper.Mzk1AxiomGateActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual

/-! # Mzk1KummerChainAcceptanceActual — acceptance over the green Kummer chain

A570 (qpilot lane, non-conflicting name): acceptance checks over the green
Kummer transport/realization chain and the axiom gate.
 -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1KummerChainAcceptanceActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1AxiomGateActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Acceptance: the Kummer power map identifies the transported q image. -/
theorem acceptance_kummerMap_thetaOne :
    kummerMap T (thetaOneCarrier T) = qPilotInThetaCarrier T :=
  kummerMap_thetaOne T

/-- Acceptance: the q image is realized as the Kummer image of the theta image. -/
theorem acceptance_qImage_realized :
    (genuineKummerData T).qImageInTheta =
      kummerMap T (genuineKummerData T).thetaImage :=
  genuineKummerData_constructed T

/-- Acceptance: the q image lies in the actual theta hull. -/
theorem acceptance_qImage_mem_hull :
    (genuineKummerData T).qImageInTheta ∈ s1902Hull T := by
  rw [show (genuineKummerData T).qImageInTheta = qPilotInThetaCarrier T from rfl]
  exact qPilotInThetaCarrier_mem_hull T

/-- Acceptance: the paper Kummer reading is strict. -/
theorem acceptance_paperReading_strict (R : PaperKummerReading T) :
    R.qReading < R.thetaReading :=
  paperKummerReading_strict T R

#check acceptance_kummerMap_thetaOne
#check acceptance_qImage_realized
#check acceptance_paperReading_strict

end LeanFormal.IUT.XiFPaper.Mzk1KummerChainAcceptanceActual
end
