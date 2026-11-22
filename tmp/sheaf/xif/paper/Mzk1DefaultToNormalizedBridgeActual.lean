/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.QVFamPureFractionalScalingDataGapActual
import Mathlib.Tactic
/-! # Conditional bridge: coefficient equality gives the existing normalized scaling data -/

The default-norm variant is type-compatible but its norm proposition is default,
while `ArithmeticTuplePureFractionalScalingData` uses the normalized instance.
The exact bridge is `qVFamNormalizedCoefficient = qVFamPureCoefficient`; given it,
the existing normalized generator supply and production constructor close the data.
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1DefaultToNormalizedBridgeActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
/-- Exact coefficient bridge: normalized coefficient equals the default pure coefficient. -/
def QVFamNormalizedCoefficientBridge : Prop :=
  qVFamNormalizedCoefficient T b = qVFamPureCoefficient T b ()
/-- Conditional normalized generator supply from the coefficient bridge. -/
noncomputable def normalizedGeneratorSupply_of_coefficient_bridge
    (h : QVFamNormalizedCoefficientBridge T b) : NormalizedGeneratorSupply T b :=
  qVFamNormalizedGeneratorSupply_of_coefficient_eq T b h
/-- Conditional production scaling data at the default pure coefficient. -/
noncomputable def pureFractionalScalingData_of_coefficient_bridge
    (h : QVFamNormalizedCoefficientBridge T b) :
    ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple (qVFamPureCoefficient T b) :=
  qVFamPureFractionalScalingData_of_supply T b
    (normalizedGeneratorSupply_of_coefficient_bridge T b h)
/-- The exact missing bridge (not asserted). -/
def QVFamNormalizedCoefficientBridgeMissing : Prop :=
  QVFamNormalizedCoefficientBridge T b
end LeanFormal.IUT.XiFPaper.Mzk1DefaultToNormalizedBridgeActual
end