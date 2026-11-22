/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C17NativeBaseResidueOneActual
import tmp.sheaf.xif.paper.Mzk1C17QCANDResNormComapActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1C17BothResidueFieldInputsGapActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResidueFieldEquivActual
open LeanFormal.IUT.XiFPaper.Mzk1C17NativeBaseResidueOneActual
open LeanFormal.IUT.XiFPaper.Mzk1C17QCANDResNormComapActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
def QVFamResidueFieldEquivInput : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    ResidueFieldEquiv
      (p := (comap (k := T.arithmetic.Fmod) (qVFamTensorPlace T b)).maximalIdeal.asIdeal)
      (P := (qVFamTensorPlace T b).maximalIdeal.asIdeal)
theorem resNormDegreeGap_of_both_residueFieldInputs
    (hbase : NativeBaseResidueFieldEquivInput T)
    (hF : QVFamResidueFieldEquivInput T) :
    ResNormDegreeGap T := by
  intro b
  have hb := localResidueDegree_nativeBase_eq_one_of_input T hbase b
  have hf : localResidueDegree (k := T.arithmetic.Fmod) (qVFamTensorPlace T b) = 1 := by
    change Ideal.inertiaDeg'
      (comap (k := T.arithmetic.Fmod) (qVFamTensorPlace T b)).maximalIdeal.asIdeal
      (qVFamTensorPlace T b).maximalIdeal.asIdeal = 1
    exact inertiaDeg'_eq_one_of_residueFieldEquiv (hF b)
  rw [hb, hf]


end LeanFormal.IUT.XiFPaper.Mzk1C17BothResidueFieldInputsGapActual
