/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C17QCANDOrderResidueActual
import Mathlib.Tactic

/-! # P6-C1: ORDER subgap in coefficient form (single cluster, CONDITIONAL) -/
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1C17QCANDOrderResidueActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
namespace LeanFormal.IUT.XiFPaper.Mzk1C17QCANDOrderCoeffActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- ORDER gap written as the coefficient equality used by the q packet. -/
theorem orderGap_imp_coefficient_eq
    (h : QCANDOrderGap T) :
    forall b : Bad (nativePlaceSelection T),
      ((baseQ T b).order : Real) = qVFamTensorCoefficient T b := by
  intro b
  rw [qVFamTensorCoefficient_eq_order, h b]

def orderCoeffRows : List (String × String × String) :=
  [ ("orderGap_imp_coefficient_eq", "baseQ order = qVFamily coefficient", "PROVED (conditional on ORDER)") ]
theorem orderCoeffRows_length : orderCoeffRows.length = 1 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1C17QCANDOrderCoeffActual
