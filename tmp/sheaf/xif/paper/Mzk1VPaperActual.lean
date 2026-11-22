/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ScaledPaper312Actual
import tmp.sheaf.xif.paper.Mzk1QSideExplicitActual
import Mathlib.Tactic

/-! # A782 hull: `V_paper` and the scaled equivalence

Definitions:
* `qSideContribution P = order · log(residueNormBase)` is the paper q-side
  magnitude `A = |log q|` (`= -qPilotLogVolumeReading P`, green QSide);
* `VPaper T P k = thetaScaledLog T k - qSideContribution P` is the scaled hull
  log-volume with the q-side contribution subtracted;
* `VPaperSSIneq s T P k = VPaper + (s-1)·qSideContribution` is the paper RHS
  after moving the `(s-1)A` coefficient term to the volume side.

Proved:
1. `qSideContribution_eq_neg_reading` (green QSide closed form);
2. `scaledPaper312_iff_VPaper_nonneg`: the scaled statement is `0 <= VPaper`;
3. `scaledPaper312_iff_ssIneq_shape`: the scaled statement is exactly
   `(s-1)·A <= VPaperSSIneq s` (definitional rearrangement).

The only remaining gap is the analytic identification
`thetaScaledLog T k = scaledClosedFormR-corrected k` (iterated Haar scaling law, shehdd).
No unconditional SSIneq is asserted. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1VPaperActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1ScaledPaper312Actual
open LeanFormal.IUT.XiFPaper.Mzk1QSideExplicitActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open scoped BigOperators ENNReal

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput l V}

/-- The paper q-side magnitude `A = |log q| = order · log(residueNormBase)`. -/
noncomputable def qSideContribution
    (P : PaperQPilotObjectActual (l := l) (I := I)) : ℝ :=
  (P.line.C3.q.order : ℝ) *
    Real.log (residueNormBase (K := I.initial.arithmetic.Fmod) ((P.line.C3.place).val))

theorem qSideContribution_eq_neg_reading
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    qSideContribution P = -qPilotLogVolumeReading P := by
  unfold qSideContribution
  rw [qPilotLogVolumeReading_eq_neg_order_mul_log P]
  ring

/-- `V_paper`: scaled θ-hull log-volume minus the q-side contribution. -/
noncomputable def VPaper
    {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]
    (P : PaperQPilotObjectActual (l := l) (I := I)) (k : ℕ) : ℝ :=
  thetaScaledLog T k + qSideContribution P

/-- The scaled paper statement in `V_paper` form: it is `0 <= VPaper`. -/
theorem scaledPaper312_iff_VPaper_nonneg
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]
    (P : PaperQPilotObjectActual (l := l) (I := I)) (k : ℕ) :
    ScaledPaper312Statement T (qPilotLogVolumeReading P) k ↔
      0 ≤ VPaper (I := I) T P k := by
  have hA := qSideContribution_eq_neg_reading P
  unfold ScaledPaper312Statement VPaper
  rw [hA]
  constructor <;> intro h <;> linarith

/-- The paper-RHS form: `VPaperSSIneq s = VPaper + (s-1)·A`; the scaled statement
is exactly `(s-1)A <= VPaperSSIneq s`. -/
noncomputable def VPaperSSIneq
    {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]
    (P : PaperQPilotObjectActual (l := l) (I := I)) (s : ℝ) (k : ℕ) : ℝ :=
  VPaper (I := I) T P k + (s - 1) * qSideContribution P

theorem scaledPaper312_iff_ssIneq_shape
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]
    (P : PaperQPilotObjectActual (l := l) (I := I)) (s : ℝ) (k : ℕ) :
    ScaledPaper312Statement T (qPilotLogVolumeReading P) k ↔
      (s - 1) * qSideContribution P ≤ VPaperSSIneq (I := I) T P s k := by
  have hA := qSideContribution_eq_neg_reading P
  unfold ScaledPaper312Statement VPaperSSIneq VPaper
  rw [hA]
  constructor <;> intro h <;> linarith

def vpaperRows : List (String × String × String) :=
  [ ("q contribution", "qSideContribution P = order·log residueNormBase = -qPilotLogVolumeReading P = A", "PROVED (qSideContribution_eq_neg_reading)"),
    ("V_paper", "VPaper T P k = thetaScaledLog T k - qSideContribution P", "DEF"),
    ("scaled statement", "ScaledPaper312Statement ↔ 0 <= VPaper", "PROVED (scaledPaper312_iff_VPaper_nonneg)"),
    ("SSIneq form", "ScaledPaper312Statement ↔ (s-1)A <= VPaper + (s-1)A = VPaperSSIneq s", "PROVED (scaledPaper312_iff_ssIneq_shape)"),
    ("remaining gap", "thetaScaledLog T k = corrected scaledClosedFormR k (iterated Haar scaling law)", "ANALYTIC GAP (shehdd A775-1)") ]

theorem vpaperRows_length : vpaperRows.length = 5 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1VPaperActual.qSideContribution_eq_neg_reading
#print axioms LeanFormal.IUT.XiFPaper.Mzk1VPaperActual.scaledPaper312_iff_VPaper_nonneg
#print axioms LeanFormal.IUT.XiFPaper.Mzk1VPaperActual.scaledPaper312_iff_ssIneq_shape

end LeanFormal.IUT.XiFPaper.Mzk1VPaperActual

end