/- Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import Mathlib.Tactic

/-! A533: Kummer realization — reduce `GenuineKummerData.qImage_realized` to a theorem.

In `Mzk1KummerTransportActual` the q-pilot realization in the THETA carrier is
proved: `qPilotInThetaCarrier = kummerMap thetaOneCarrier` (from the SHE root
relation).  A completion-valued transport is impossible (S342/S1929), so this is the
strongest genuine form of `qImage_realized`.

This file:
* re-exports the realized equality for `genuineKummerData`;
* combines the strict-volume xi-e realization with the paper readout
  identifications: if the q-pilot reading is the log-volume of the q-image and the
  Theta reading is the log-volume of the hull, the strict signed inequality
  `qReading < thetaReading` follows (no reflexivity). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open scoped BigOperators

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- **`qImage_realized` as a THEOREM** for the genuine Kummer data: the q-pilot
image in the theta carrier is the Kummer image of the theta image. -/
theorem qImage_realized :
    (genuineKummerData T).qImageInTheta =
      kummerMap T (genuineKummerData T).thetaImage :=
  genuineKummerData_constructed T

/-- The theta image of the genuine data is the label-1 theta image. -/
theorem thetaImage_realized :
    (genuineKummerData T).thetaImage = thetaOneCarrier T := rfl

/-- The realized q-pilot image is contained in the actual Theta hull. -/
theorem qImage_realized_mem_hull :
    (genuineKummerData T).qImageInTheta ∈ s1902Hull T := by
  simpa [genuineKummerData] using qPilotInThetaCarrier_mem_hull T

/-! ## Paper readout bridge (minimal named identifications) -/

/-- The paper signed readings linked to the realized volume data.  The equalities
`qReading_log`/`thetaReading_log` are the minimal remaining named identifications of
the paper readings with the realized log-volumes (1-column multiradial comparison);
they are explicit fields, not definitional equalities. -/
structure PaperKummerReading where
  D : KummerXiERealization T
  qReading : Real
  thetaReading : Real
  qReading_log : qReading = Real.log (D.vol {qPilotInThetaCarrier T})
  thetaReading_log : thetaReading = Real.log (D.vol (s1902Hull T))

/-- **Strict signed inequality from the realized strict volume increase**:
`qReading < thetaReading` (no reflexivity; the strict_measure field is the
non-vacuity witness of shehdd's XiEContainmentRequirement). -/
theorem paperKummerReading_strict (R : PaperKummerReading T) :
    R.qReading < R.thetaReading := by
  rw [R.qReading_log, R.thetaReading_log]
  exact Real.log_lt_log R.D.q_pos R.D.strict_measure

/-- The non-strict paper signed inequality. -/
theorem paperKummerReading_le (R : PaperKummerReading T) :
    R.qReading ≤ R.thetaReading :=
  le_of_lt (paperKummerReading_strict T R)

/-- C_Theta form: if the Theta reading is `C * |log q|` and the q reading is
`-|log q|` with `|log q| > 0`, the strict inequality gives `-1 < C` (hence
`C >= -1`). -/
theorem paperKummerReading_CTheta {qMag C qReading thetaReading : Real}
    (hq : 0 < qMag) (hqeq : qReading = -qMag)
    (hthetaeq : thetaReading = C * qMag)
    (hstrict : qReading < thetaReading) : -1 < C := by
  rw [hqeq, hthetaeq] at hstrict
  nlinarith

end LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual