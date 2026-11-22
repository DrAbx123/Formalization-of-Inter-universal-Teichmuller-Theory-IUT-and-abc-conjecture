/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.PaperLevelXiFTargetBridgeActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import Mathlib.Tactic

/-! # Wire the actual hull-containment xi-f inequality to the actual magnitude target

The hull-containment route (`PaperLevelXiFTargetProofActual` +
`PaperLevelXiFTargetBridgeActual`) proves the ACTUAL target from per-b normalized-log
monotonicity of the actual root hull containment
`qPilotNormRegion ⊆ rootThetaHull`, using the actual normalized coefficients
`qVFamNormalizedCoefficientFamily` (no default-norm model, no S45, no ratio=1).
This file exposes the exact magnitude form of that target. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ActualHullTargetMagnitudeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetBridgeActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- **Actual target magnitude (unconditional, hull-containment route).** -/
theorem actualTargetMagnitude_actual :
    ActualPaperXiFTargetMagnitude (l := l) T :=
  (actualPaperXiFTarget_iff_magnitude (l := l) T).mp
    (actualPaperXiFTarget (l := l) T)

/-- Signed form (already the target definition). -/
theorem actualTargetSigned_actual : ActualPaperXiFTarget (l := l) T :=
  actualPaperXiFTarget (l := l) T

/-- Per-b actual inequality re-export. -/
theorem actualPerB_inequality (b : Bad (nativePlaceSelection T)) :
    perBQPilotLog T b ≤ perBThetaHullLog T b :=
  perBQPilotLog_le_perBThetaHullLog (l := l) T b

def actualHullTargetRows : List (String × String × String) :=
  [ ("actualTargetMagnitude_actual", "actualThetaHullMagnitudeRoot ≤ actualQPilotMagnitudeClassical (unconditional, hull containment)", "PROVED"),
    ("actualTargetSigned_actual", "actualQPilotSignedLogClassical ≤ actualThetaHullLogRoot", "PROVED"),
    ("actualPerB_inequality", "perBQPilotLog ≤ perBThetaHullLog (actual root hull containment)", "PROVED"),
    ("route", "actual normalized hull containment (no S45, no ratio=1, no default-norm model)", "ACCEPTED ROUTE (pending lead audit)") ]

theorem actualHullTargetRows_length : actualHullTargetRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ActualHullTargetMagnitudeActual

end