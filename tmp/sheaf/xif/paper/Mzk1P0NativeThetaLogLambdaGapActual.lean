/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0NativeComparisonLatticeActual
import tmp.sheaf.xif.paper.Mzk1P2NativeBlockAlignmentActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import Mathlib.Tactic
/-! # 语义差（#1 路线修正）

nativeThetaReadout 是单因子 native tensor block 的 raw Haar log-volume：
qVFamTensorPlaces T b 单点、qVFamTensorTuple 单因子，区域是 local log-shell
在 one-factor tensor 中的像，测度是 Measure.addHaar，没有 unit-ball 归一化。

它不是 paper 3.12 的 theta hull 读数。Paper theta 侧是 root-extension product hull
的 normalized log：s1915ClosedForm = 1 + Σ_b d_b log r_b（closedForm_eq_one_add_normalizedLog
+ s1915_local_measure）。两者之间缺的是 tensor/product carrier isometry 与
det/degree 归一化因子，不能把 nativeThetaReadout 直接当 paper theta。

因此 #1 不能用 NativeThetaLogLambdaBridge/R37/product 对齐收口；正确目标见
NativeThetaPaperReadoutGap：比较 nativeQReadout 与 paper normalized theta 读数，
并用 logMass_eq_add_log_factor/addHaarScalarFactor 写出显式因子。
-/
/-! #1: exact tensor/product obstruction for the theta-log-lambda bridge -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeThetaLogLambdaGapActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeComparisonLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1P2NativeBlockAlignmentActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutActual
open MeasureTheory
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
/-- Native theta readout is the raw tensor Haar log-volume (no unit-ball normalization). -/
theorem nativeThetaReadout_eq_log_localLogShell :
    nativeThetaReadout T b =
      Real.log ((nativeTensorHaar (p := qVFamTensorP T b)
        (qVFamTensorPlaces T b) qVFamTensorTuple)
        (nativeTensorRegion (p := qVFamTensorP T b)
          (qVFamTensorPlaces T b) qVFamTensorTuple)).toReal := rfl

theorem nativeThetaReadout_eq_rawTensorHaar :
    nativeThetaReadout T b =
      (haarLogVolume (nativeTensorHaar (p := qVFamTensorP T b)
        (qVFamTensorPlaces T b) qVFamTensorTuple)
        (nativeTensorRegion (p := qVFamTensorP T b)
          (qVFamTensorPlaces T b) qVFamTensorTuple)).toReal := rfl
/-- The comparison follows from the exact theta/log-lambda bridge. -/
theorem nativeComparison_of_NativeThetaLogLambdaBridge
    (h : NativeThetaLogLambdaBridge T b) :
    nativeQReadout T b ≤ nativeThetaReadout T b :=
  le_trans (nativeQReadout_le_log_lambda T b) h
/-- Exact missing interface: tensor-product Haar vs local root-extension Haar. -/
def NativeTensorProductAlignmentMissing : Prop :=
  NativeThetaLogLambdaBridge T b
/-- Obstruction record: no canonical alignment between native tensor block and
the product carrier of root extensions is available in the tree. -/
def NativeTensorProductAlignmentObstruction : List String :=
  p2NativeProductBlockMissing
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeThetaLogLambdaGapActual
end
