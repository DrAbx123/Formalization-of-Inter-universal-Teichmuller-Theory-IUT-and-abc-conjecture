/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.n8.closure.C3Roots
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import Mathlib.Tactic
/-! # P0: native source root/tensor core (no old empty C3) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeSourceCoreActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
universe u
variable {l : PrimeGeFive}
structure NativeSourceCore (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  roots : NatRootSystem (unitToAlgClosed
    (Units.mk0 (qVFamily T b).q (qVFamily T b).q_ne_zero))
  tensorBlock : Type
  qCoeff : Real
noncomputable def actualNativeSourceCore (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : NativeSourceCore T b where
  roots := qCandidateRootSystem (qVFamTensorPlace T b) (qVFamily T b)
  tensorBlock := qVFamTensorBlock T b
  qCoeff := qVFamTensorCoefficient T b
theorem nativeCore_roots_pow_self (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) (n : Nat) (hn : n ≠ 0) :
    (actualNativeSourceCore T b).roots.root n ^ n =
      unitToAlgClosed (Units.mk0 (qVFamily T b).q (qVFamily T b).q_ne_zero) :=
  NatRootSystem.pow_self _ n hn
theorem nativeCore_qCoeff_nonneg (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    0 ≤ (actualNativeSourceCore T b).qCoeff :=
  qVFamTensorCoefficient_nonneg T b
theorem nativeCore_qCoeff_eq (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    (actualNativeSourceCore T b).qCoeff = ((qVFamily T b).order : Real) := rfl
def rows : List String := ["roots in AlgebraicClosure", "tensorBlock qVFamTensorBlock", "qCoeff qVFamTensorCoefficient", "no SourcePilotRegionData"]
theorem rows_length : rows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeSourceCoreActual
end