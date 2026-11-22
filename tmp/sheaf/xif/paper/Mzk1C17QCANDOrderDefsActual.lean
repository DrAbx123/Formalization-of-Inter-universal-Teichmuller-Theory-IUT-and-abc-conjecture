/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C17QCANDOrderResidueActual
import Mathlib.Tactic

/-! # P6-D1: QCAND ORDER definitions (single cluster, definition-level) -/
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
namespace LeanFormal.IUT.XiFPaper.Mzk1C17QCANDOrderDefsActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

def baseQOrder : Nat := (baseQ T b).order
def qVFamOrder : Nat := (qVFamily T b).order

theorem baseQOrder_eq : baseQOrder T b = (baseQ T b).order := rfl
theorem qVFamOrder_eq : qVFamOrder T b = (qVFamily T b).order := rfl
theorem qVFamTensorCoefficient_eq_qVFamOrder :
    qVFamTensorCoefficient T b = (qVFamOrder T b : Real) := rfl

def orderDefRows : List (String × String × String) :=
  [ ("baseQOrder_eq", "baseQ order projection", "DEF"),
    ("qVFamOrder_eq", "qVFamily order projection", "DEF"),
    ("qVFamTensorCoefficient_eq_qVFamOrder", "coefficient = order cast", "PROVED") ]
theorem orderDefRows_length : orderDefRows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1C17QCANDOrderDefsActual
