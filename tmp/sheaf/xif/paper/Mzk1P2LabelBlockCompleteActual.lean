/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P2LabelBlockCoefficientActual
import Mathlib.Tactic

/-! # P2: four-source rank-one label block prototype `(p,label)` -/

/-
| field | value |
|---|---|
| Status | PROVED: source Q (`c0QHat`), source theta (`rootNormedThetaValueInL`), landing (identity), weight (finrank); Q = λ·c and Q lies in the allowed λO |
| GAP | multi-index tuple / tensor landing and allowed re-root operations are not constructed; theta-membership is handled in `Mzk1P2ThetaAllowedImageActual` |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCompleteActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory
open scoped BigOperators ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- One actual rank-one label block: a bad place and one signed theta label. -/
structure P2ActualLabelBlock where
  b : Bad (nativePlaceSelection T)
  label : SignedLabel l.value

/-- Source 1: the local prime. -/
noncomputable def p2BlockP (A : P2ActualLabelBlock T) : Nat := qVFamTensorP T A.b

/-- Source 2: the source Q generator `qhat = alpha^{2l}`. -/
noncomputable def p2BlockSourceQ (A : P2ActualLabelBlock T) : rootNormedExtension T A.b :=
  c0QHat T A.b

/-- Source 3: the source theta value. -/
noncomputable def p2BlockSourceTheta (A : P2ActualLabelBlock T) : rootNormedExtension T A.b :=
  rootNormedThetaValueInL T A.b A.label

/-- Source 4: the landing into `L_b`. -/
noncomputable def p2BlockLanding (A : P2ActualLabelBlock T) : rootNormedExtension T A.b :=
  p2BlockSourceTheta T A

/-- Weight: the local degree. -/
noncomputable def p2BlockWeight (A : P2ActualLabelBlock T) : Nat :=
  Module.finrank ℚ_[qVFamTensorP T A.b] (rootNormedExtension T A.b)

/-- R1.2 expansion: `Q = λ_b · c_b`. -/
theorem p2Block_sourceQ_eq_lambda_mul_coeff (A : P2ActualLabelBlock T) :
    p2BlockSourceQ T A = rootThetaFieldLambda T A.b * p2Coefficient T A.b :=
  p2QHat_eq_lambda_mul_coefficient T A.b

/-- Source Q lies in the allowed λO region. -/
theorem p2Block_sourceQ_mem_allowed (A : P2ActualLabelBlock T) :
    p2BlockSourceQ T A ∈ rootThetaFieldLambdaO T A.b := by
  unfold p2BlockSourceQ rootThetaFieldLambdaO
  exact ⟨p2Coefficient T A.b, p2Coefficient_mem_unitBall T A.b,
    (p2QHat_eq_lambda_mul_coefficient T A.b).symm⟩

/-- Four-source consistency for the block (theta membership in the companion file). -/
theorem p2Block_four_sources (A : P2ActualLabelBlock T) :
    p2BlockSourceQ T A = rootThetaFieldLambda T A.b * p2Coefficient T A.b
      ∧ p2BlockLanding T A = p2BlockSourceTheta T A
      ∧ p2BlockWeight T A = Module.finrank ℚ_[qVFamTensorP T A.b] (rootNormedExtension T A.b) := by
  exact ⟨p2Block_sourceQ_eq_lambda_mul_coeff T A, rfl, rfl⟩

end LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCompleteActual