/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C17QCANDOrderResidueActual
import Mathlib.Tactic

/-! # P6-D2: QCAND ORDER iff coefficient equality (single cluster) -/
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Mzk1C17QCANDOrderResidueActual
namespace LeanFormal.IUT.XiFPaper.Mzk1C17QCANDOrderDefEqActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem orderGap_iff_coefficient_eq :
    QCANDOrderGap T ↔
      forall b : Bad (nativePlaceSelection T),
        ((baseQ T b).order : Real) = qVFamTensorCoefficient T b := by
  constructor
  · intro h b
    rw [qVFamTensorCoefficient_eq_order, h b]
  · intro h b
    have hb : ((baseQ T b).order : Real) = ((qVFamily T b).order : Real) := by
      simpa [qVFamTensorCoefficient] using h b
    exact_mod_cast hb

def orderDefEqRows : List (String × String × String) :=
  [ ("orderGap_iff_coefficient_eq", "ORDER gap iff coefficient equality", "PROVED") ]
theorem orderDefEqRows_length : orderDefEqRows.length = 1 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1C17QCANDOrderDefEqActual
