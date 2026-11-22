/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1B5ContractEvidenceActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1B5ContractEvidenceConsumerActual

open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.Mzk1B5ContractEvidenceActual
open LeanFormal.IUT.XiFPaper.Mzk1C17QCANDResNormComapActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
theorem residueNormBase_eq_pow_of_evidence
    (E : B5ContractEvidence T) (v : NumberField.FinitePlace T.arithmetic.K) :
    residueNormBase v = ((residueCharacteristic v : ℕ) : ℝ) ^
      (Ideal.span {(residueCharacteristic v : ℤ)}).inertiaDeg'
        v.maximalIdeal.asIdeal :=
  E.norm_eq_pow v
theorem log_residueNormBase_eq_pow_of_evidence
    (E : B5ContractEvidence T) (v : NumberField.FinitePlace T.arithmetic.K) :
    Real.log (residueNormBase v) =
      ((Ideal.span {(residueCharacteristic v : ℤ)}).inertiaDeg'
        v.maximalIdeal.asIdeal : ℝ) * Real.log (residueCharacteristic v : ℝ) :=
  E.log_norm_eq_pow v
theorem resNormDegreeGap_of_evidence (E : B5ContractEvidence T) : ResNormDegreeGap T :=
  E.residue_gap


end LeanFormal.IUT.XiFPaper.Mzk1B5ContractEvidenceConsumerActual
