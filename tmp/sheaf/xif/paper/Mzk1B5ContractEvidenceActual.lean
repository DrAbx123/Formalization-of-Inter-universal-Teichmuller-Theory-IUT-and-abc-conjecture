/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1B5ResidueNormPowActual
import tmp.sheaf.xif.paper.Mzk1C17BothResidueFieldInputsGapActual
import tmp.sheaf.xif.paper.Mzk1C17NativeBaseResidueOneActual
import Mathlib.Tactic

/-! # B5 contract evidence: norm power + absolute dimension + residue gap -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.Mzk1B5ContractEvidenceActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1B5ResidueNormPowActual
open LeanFormal.IUT.XiFPaper.Mzk1C17NativeBaseResidueOneActual
open LeanFormal.IUT.XiFPaper.Mzk1C17BothResidueFieldInputsGapActual
open LeanFormal.IUT.XiFPaper.Mzk1C17QCANDResNormComapActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
structure B5ContractEvidence : Prop where
  norm_eq_pow : ∀ v : NumberField.FinitePlace T.arithmetic.K,
    residueNormBase v =
      ((residueCharacteristic v : ℕ) : ℝ) ^
        (Ideal.span {(residueCharacteristic v : ℤ)}).inertiaDeg'
          v.maximalIdeal.asIdeal
  log_norm_eq_pow : ∀ v : NumberField.FinitePlace T.arithmetic.K,
    Real.log (residueNormBase v) =
      ((Ideal.span {(residueCharacteristic v : ℤ)}).inertiaDeg'
        v.maximalIdeal.asIdeal : ℝ) * Real.log (residueCharacteristic v : ℝ)
  residue_gap : ResNormDegreeGap T
theorem b5ContractEvidence_of_inputs
    (hbase : NativeBaseResidueFieldEquivInput T)
    (hF : QVFamResidueFieldEquivInput T) :
    B5ContractEvidence T where
  norm_eq_pow := fun v => residueNormBase_eq_pow_inertiaDeg' v
  log_norm_eq_pow := fun v =>
    log_residueNormBase_eq_inertiaDeg_mul_log_residueCharacteristic v
  residue_gap := resNormDegreeGap_of_both_residueFieldInputs T hbase hF
end LeanFormal.IUT.XiFPaper.Mzk1B5ContractEvidenceActual
