/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HullUBPaperVRawBindingActual
import tmp.sheaf.xif.paper.Mzk1ThetaVLayerScaleOffsetActual
import Mathlib.Tactic
/-! # GAP-P7-THETA-V L3: actual ThetaVScaleOffset (scale=1, offset=1) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaVScaleOffsetIdentityActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1HullUBPaperVRawBindingActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaVLayerScaleOffsetActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
noncomputable def thetaVScaleOffset (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : ThetaVScaleOffset where
  rawV := s1915ClosedForm T
  normV := rootExtensionProductNormalizedLog T (s1902Hull T)
  scale := 1
  scale_pos := by norm_num
  offset := 1
  layer_eq := by
    rw [closedForm_eq_one_add_normalizedLog (T := T)]
    ring
def rows : List String := ["rawV=s1915ClosedForm", "normV=normalizedLog", "scale=1", "offset=1", "ACTUAL"]
theorem rows_length : rows.length = 5 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1ThetaVScaleOffsetIdentityActual
end