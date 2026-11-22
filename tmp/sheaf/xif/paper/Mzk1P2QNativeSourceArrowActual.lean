/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P2LabelBlockCoefficientActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import Mathlib.Tactic

/-! # P2: native q reading -> root expansion -> qhat arrow (first missing pinpointed) -/

/-
| field | value |
|---|---|
| Status | PROVED: the native qVFamily element maps into the root extension and its image is exactly `c0QHat = alpha^{2l}` (`p2NativeQImage_eq_qhat`) |
| GAP | **first missing**: the *real log reading* of the native q (`localLogMagnitude (qVFamily b)`) is not yet identified with `log‖c0QHat b‖`; also the old C3 qPilot reading lives on the empty `SourcePilotRegionData` (S1429), so it cannot be used |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P2QNativeSourceArrowActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCoefficientActual
open LeanFormal.IUT.XiFPaper.O2QrootGlueActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open MeasureTheory
open scoped BigOperators ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The native qVFamily element embedded into the root extension. -/
noncomputable def p2NativeQImage (b : Bad (nativePlaceSelection T)) :
    rootNormedExtension T b :=
  algebraMap (rootBase T b) (rootNormedExtension T b)
    ((qVFamily T b).q : rootBase T b)

/-- The embedded native q is exactly `qhat = alpha^{2l}`. -/
theorem p2NativeQImage_eq_qhat (b : Bad (nativePlaceSelection T)) :
    c0QHat T b = p2NativeQImage T b := by
  rw [c0QHat_eq_q T b]
  rfl

/-- Native real q log-magnitude at a bad place. -/
noncomputable def p2NativeQMagnitude (b : Bad (nativePlaceSelection T)) : Real :=
  localLogMagnitude (qVFamily T b)

/-- Root `qhat` **positive** log magnitude (`-log‖qhat‖`, sign-corrected). -/
noncomputable def p2RootQhatMagnitude (b : Bad (nativePlaceSelection T)) : Real :=
  -Real.log ‖c0QHat T b‖

/-- `qhat` norm equals the native qVFamily norm (`norm_algebraMap'` + `c0QHat_eq_q`). -/
theorem p2QHat_norm_eq_qVFamily_norm (b : Bad (nativePlaceSelection T)) :
    ‖c0QHat T b‖ = ‖((qVFamily T b).q : rootBase T b)‖ := by
  rw [c0QHat_eq_q T b]
  exact norm_algebraMap' (rootNormedExtension T b) ((qVFamily T b).q : rootBase T b)

/-- Bridge: the positive root `qhat` log magnitude equals the native q log magnitude. -/
theorem p2RootQhatMagnitude_eq_native (b : Bad (nativePlaceSelection T)) :
    p2RootQhatMagnitude T b = p2NativeQMagnitude T b := by
  unfold p2RootQhatMagnitude p2NativeQMagnitude localLogMagnitude localSignedLog
  rw [p2QHat_norm_eq_qVFamily_norm T b]

/-- The former “gap” is now **proved**: the native q log reading equals the
positive root `qhat` log magnitude. -/
def P2QNativeReadingGap : Prop := ∀ b : Bad (nativePlaceSelection T),
  p2NativeQMagnitude T b = p2RootQhatMagnitude T b

theorem p2QNativeReadingGap_holds : P2QNativeReadingGap T := fun b =>
  (p2RootQhatMagnitude_eq_native T b).symm

/-- Definition rows after the sign correction. -/
def p2QNativeRows : List (String × String × String) :=
  [ ("native q image", "c0QHat = algebraMap(qVFamily.q)", "PROVED")
  , ("norm bridge", "‖c0QHat‖ = ‖qVFamily.q‖", "PROVED (norm_algebraMap')")
  , ("reading bridge", "-log‖c0QHat‖ = localLogMagnitude(qVFamily)", "PROVED")
  , ("former gap", "P2QNativeReadingGap", "PROVED (sign was fixed)")
  , ("remaining", "P.line.C3.q vs qVFamily same-origin map; old C3 empty (S1429)", "GAP") ]

theorem p2QNativeRows_length : p2QNativeRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P2QNativeSourceArrowActual