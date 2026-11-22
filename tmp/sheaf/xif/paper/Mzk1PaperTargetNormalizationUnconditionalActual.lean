/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PaperTargetNormalizationActual
import tmp.sheaf.xif.paper.Mzk1PaperBlockTargetActual
import tmp.sheaf.xif.paper.S778PaperQPilotHalfRegionActual
import Mathlib.Tactic

/-! # Unconditional paper-faithful block target (P0-A / P4-B)

Discharges the explicit positivity/finiteness hypotheses of
`Mzk1PaperTargetNormalizationActual.paperTargetNormalization_of_pos_fin` using:
* `qPilotPaperRegion_measure_pos` (S778, actual additive Haar);
* `Mzk1PaperBlockTargetActual.paperHull_measure_lt_top` (S800 least-hull finite via F(0)O=O_hol).

No coefficient bridge and no new target hypothesis is used.  The old conditional theorem is untouched.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperTargetNormalizationUnconditionalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S800LeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S778PaperQPilotHalfRegionActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperTargetNormalizationActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperBlockTargetActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]
variable (mu : Measure (qVFamTensorBlock T b))
variable [Measure.IsAddHaarMeasure mu]

theorem paperTargetNormalization_unconditional :
    PaperTargetNormalization (l := l) T b mu :=
  paperTargetNormalization_of_pos_fin (l := l) T b mu
    (qPilotPaperRegion_measure_pos (l := l) T b mu)
    (Mzk1PaperBlockTargetActual.paperHull_measure_lt_top (l := l) T b mu)

theorem paperM_nonneg_unconditional :
    0 ≤ paperM (l := l) T b mu :=
  paperM_nonneg_of_target (l := l) T b mu
    (paperTargetNormalization_unconditional (l := l) T b mu)

def rows : List (String × String × String) :=
  [ ("paperTargetNormalization_unconditional", "PaperTargetNormalization", "PROVED"),
    ("paperM_nonneg_unconditional", "0 ≤ paperM", "PROVED"),
    ("coefficient bridge", "not used", "AVOIDED") ]

theorem rows_length : rows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1PaperTargetNormalizationUnconditionalActual

end