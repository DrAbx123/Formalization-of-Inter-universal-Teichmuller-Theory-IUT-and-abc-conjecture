/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ScaledPaper312Actual
import tmp.sheaf.xif.paper.Mzk1ScaledThetaHullShaActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import tmp.sheaf.xif.paper.Mzk1ThetaVLayerScaleOffsetActual
import Mathlib.Tactic

/-! # GAP-P7-THETA-V L4: general-k scale/offset with qLogSum (conditional) -/
noncomputable section
set_option maxHeartbeats 2000000
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped BigOperators NumberField
open LeanFormal.IUT.IUTIV.Estimates
namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaVScaleOffsetGeneralActual
open LeanFormal.IUT.XiFPaper.Mzk1ScaledPaper312Actual
open LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullShaActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaVLayerScaleOffsetActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [Nonempty (Bad (nativePlaceSelection T))]

/-- Conditional general-k dictionary: under the actual scaled closed-form identity,
`rawV = thetaScaledLog k`, `normV = s1915ClosedForm`, `scale = 1`,
`offset = -k * qLogSum` give an actual `ThetaVScaleOffset`. -/
theorem thetaVScaleOffset_of_closedForm (k : ℕ)
    (h : thetaScaledLog T k = scaledClosedFormR T (k : ℝ)) :
    ∃ D : ThetaVScaleOffset,
      D.rawV = thetaScaledLog T k ∧
      D.normV = s1915ClosedForm T ∧ D.scale = 1 ∧
      D.offset = -((k : ℝ) * qLogSum T) := by
  refine ⟨{
    rawV := thetaScaledLog T k
    normV := s1915ClosedForm T
    scale := 1
    scale_pos := by norm_num
    offset := -((k : ℝ) * qLogSum T)
    layer_eq := ?_ }, rfl, rfl, rfl, rfl⟩
  rw [h, scaledClosedFormR_eq]
  ring

def thetaVGeneralRows : List (String × String) :=
  [ ("thetaVScaleOffset_of_closedForm", "conditional general-k construction"),
    ("rawV/normV/scale/offset", "thetaScaledLog / s1915ClosedForm / 1 / -k*qLogSum"),
    ("unconditional closed form", "GAP") ]
theorem thetaVGeneralRows_length : thetaVGeneralRows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1ThetaVScaleOffsetGeneralActual
