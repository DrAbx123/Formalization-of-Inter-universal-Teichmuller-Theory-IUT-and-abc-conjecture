/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P2LabelBlockCompleteActual
import tmp.sheaf.xif.paper.Mzk1A1LatticeCompareActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import tmp.sheaf.xif.paper.PaperC3ThetaRootActual
import Mathlib.Tactic
/-! # A1 route §1.2/§1.3: actual multi-label theta data and q-lattice landing

At one actual bad place b the source q generator is the actual qhat, while the
Theta source hull is the closed ball lambda * O with lambda the maximizing theta
value.  Every actual signed theta label j gives a theta generator theta_j with
theta_j = lambda * d_j, d_j in the actual integer ring O.  The q generator is
the actual single-generator expansion qhat = lambda * c, c in O; it lies in the
actual theta lattice.  No artificial if-then-else support and no label average is
used: all label coefficients are actual ratios theta_j/lambda.
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A1SourceGeneratorExpansionActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCompleteActual
open LeanFormal.IUT.XiFPaper.Mzk1A1LatticeInverseActual
open LeanFormal.IUT.XiFPaper.Mzk1A1LatticeCompareActual
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open scoped BigOperators
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
/-- The actual maximizing-label block at b. -/
noncomputable def a1SourceBlock : P2ActualLabelBlock T :=
  { b := b, label := thetaLabelToSigned (rootThetaMaxIndex T b) }
/-- Source q generator: the actual qhat. -/
noncomputable def a1SourceQ : rootNormedExtension T b := c0QHat T b
/-- The actual theta generator at an arbitrary signed theta label. -/
noncomputable def a1ThetaGenerator (j : ThetaLabel (l := l)) : rootNormedExtension T b :=
  rootNormedThetaValueInL T b (thetaLabelToSigned j)
theorem a1SourceTheta_eq_fieldLambda :
    a1ThetaGenerator T b (rootThetaMaxIndex T b) = rootThetaFieldLambda T b := rfl
/-- The R1.2 coefficient. -/
noncomputable def a1Coefficient : rootNormedExtension T b := p2Coefficient T b
theorem a1Coefficient_mem_integerRing :
    a1Coefficient T b ∈ rootExtensionUnitBall T b :=
  p2Coefficient_mem_unitBall T b
/-- R1.2 actual single-generator expansion: qhat = theta_max * c. -/
theorem a1SourceQ_expansion :
    a1SourceQ T b = rootThetaFieldLambda T b * a1Coefficient T b := by
  unfold a1SourceQ a1Coefficient rootThetaFieldLambda
  exact p2QHat_eq_lambda_mul_coefficient T b
/-- Actual coefficient of the theta label j relative to the maximizing generator. -/
noncomputable def a1ThetaLabelCoefficient (j : ThetaLabel (l := l)) :
    rootNormedExtension T b :=
  a1ThetaGenerator T b j / rootThetaFieldLambda T b
/-- Each actual theta label coefficient lies in the actual integer ring O. -/
theorem a1ThetaLabelCoefficient_mem_integerRing (j : ThetaLabel (l := l)) :
    a1ThetaLabelCoefficient T b j ∈ rootExtensionUnitBall T b := by
  have hpos : 0 < ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ := by
    rw [← rootImageRadius_eq_norm_fieldLambda]
    exact rootImageRadius_pos (T := T) (b := b)
  have hle := rootThetaMaxIndex_spec (T := T) (b := b) j
  unfold rootExtensionUnitBall
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  unfold a1ThetaLabelCoefficient
  rw [norm_div]
  exact (div_le_one hpos).mpr hle
/-- Actual multi-label relation: every theta generator is lambda times its actual coefficient. -/
theorem a1ThetaGenerator_eq_lambda_mul_labelCoefficient (j : ThetaLabel (l := l)) :
    a1ThetaGenerator T b j =
      rootThetaFieldLambda T b * a1ThetaLabelCoefficient T b j := by
  have hne : rootThetaFieldLambda T b ≠ 0 := by
    intro h
    have hpos : 0 < ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ := by
      rw [← rootImageRadius_eq_norm_fieldLambda]
      exact rootImageRadius_pos (T := T) (b := b)
    rw [h, norm_zero] at hpos
    exact lt_irrefl _ hpos
  unfold a1ThetaLabelCoefficient
  field_simp [hne]
/-- Every actual theta label lands in the actual theta lattice. -/
theorem a1AllThetaLabels_mem_thetaLattice (j : ThetaLabel (l := l)) :
    a1ThetaGenerator T b j ∈ lambdaLattice T b := by
  refine ⟨a1ThetaLabelCoefficient T b j,
    a1ThetaLabelCoefficient_mem_integerRing T b j, ?_⟩
  exact (a1ThetaGenerator_eq_lambda_mul_labelCoefficient T b j).symm
/-- Source q generator lands in the actual theta lattice. -/
theorem a1SourceQ_mem_thetaLattice :
    a1SourceQ T b ∈ lambdaLattice T b := by
  refine ⟨a1Coefficient T b, a1Coefficient_mem_integerRing T b, ?_⟩
  exact (a1SourceQ_expansion T b).symm
/-- Four-source consistency with actual multi-label theta coefficients. -/
theorem a1FourSources :
    a1SourceQ T b = rootThetaFieldLambda T b * a1Coefficient T b
      ∧ a1SourceQ T b ∈ lambdaLattice T b
      ∧ a1Coefficient T b ∈ rootExtensionUnitBall T b
      ∧ (∀ j : ThetaLabel (l := l),
          a1ThetaGenerator T b j ∈ lambdaLattice T b) :=
  ⟨a1SourceQ_expansion T b, a1SourceQ_mem_thetaLattice T b,
    a1Coefficient_mem_integerRing T b, a1AllThetaLabels_mem_thetaLattice T b⟩
/-- Generatorwise q-lattice inclusion into the theta lattice. -/
theorem a1QLattice_generatorwise_subset :
    ∀ y : rootNormedExtension T b, y ∈ rootExtensionUnitBall T b →
      c0QHat T b * y ∈ lambdaLattice T b := by
  intro y hy
  refine ⟨p2Coefficient T b * y, ?_, ?_⟩
  · unfold rootExtensionUnitBall at hy ⊢
    rw [Metric.mem_closedBall, dist_eq_norm] at hy ⊢
    simp only [sub_zero] at hy ⊢
    rw [norm_mul]
    calc ‖p2Coefficient T b‖ * ‖y‖ ≤ 1 * 1 :=
          mul_le_mul (p2Coefficient_norm_le_one T b) hy (norm_nonneg _) zero_le_one
      _ = 1 := mul_one 1
  · rw [p2QHat_eq_lambda_mul_coefficient T b]
    ring
end LeanFormal.IUT.XiFPaper.Mzk1A1SourceGeneratorExpansionActual
end