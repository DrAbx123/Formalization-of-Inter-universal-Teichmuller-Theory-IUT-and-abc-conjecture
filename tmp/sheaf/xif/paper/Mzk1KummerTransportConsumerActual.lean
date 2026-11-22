/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import Mathlib.Tactic

/-!
# Mzk1KummerTransportConsumerActual — consumers of the green Kummer transport

A543: with `Mzk1KummerTransportActual` EXIT=0, this file records its two
consumer-facing results:
* the Kummer power map identifies the transported q-pilot image with
  `(theta label 1)^(2l)` (`kummerMap_thetaOne`), and
* no completion-valued right-inverse transport exists (S342/S1929 obstruction).

No new axiom. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1KummerTransportConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Consumer form: the Kummer (2l-power) image of the label-1 theta image is the
transported q-pilot image (SHE root relation). -/
theorem kummerMap_thetaOne_consumer :
    kummerMap T (thetaOneCarrier T) = qPilotInThetaCarrier T :=
  kummerMap_thetaOne T

/-- Consumer form: the genuinely realized q-image equals the Kummer image of the
theta image. -/
theorem genuineKummerData_qImage_consumer :
    (genuineKummerData T).qImageInTheta =
      kummerMap T (genuineKummerData T).thetaImage :=
  genuineKummerData_constructed T

/-- Consumer form of the S342/S1929 obstruction: there is no completion-valued
transport that is a right inverse of `completionToRootExtension` and sends the
label-1 theta image to the q-pilot completion image. -/
theorem no_completion_transport :
    ¬ ∃ F : S1902Carrier T → LiteralCompletionIQCarrier T,
      (∀ x : S1902Carrier T, completionToRootExtension T (F x) = x) ∧
        F (thetaOneCarrier T) = qPilotCompletionImage T := by
  rintro ⟨F, hright, hq⟩
  exact no_completion_valued_kummerTransport T F hright hq

/-- Consumer form: the realized q-pilot image lies in the actual Theta hull. -/
theorem qPilotInThetaCarrier_mem_hull_consumer :
    qPilotInThetaCarrier T ∈ s1902Hull T :=
  qPilotInThetaCarrier_mem_hull T

#check kummerMap_thetaOne_consumer
#check no_completion_transport

end LeanFormal.IUT.XiFPaper.Mzk1KummerTransportConsumerActual
end
