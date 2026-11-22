import tmp.sheaf.xif.paper.S657RootSignedHullIndependentActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S679DirectScalarComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.S657RootSignedHullIndependentActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Exact arithmetic coefficient of the root theta average:
`sum_j j^2 / (2l * card)`. -/
noncomputable def rootThetaAverageCoefficient : Real :=
  (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real)) /
    (2 * (l.value : Real) * (Fintype.card (SignedLabel l.value) : Real))

/-- Classical per-b qVFamily q-pilot magnitude: order(q_v) * log p_v. -/
noncomputable def qVFamLocalQPilotMagnitude : Real :=
  qVFamTensorCoefficient T b * Real.log (qVFamTensorP T b : Real)

theorem qVFamLocalQPilotMagnitude_nonneg :
    0 ≤ qVFamLocalQPilotMagnitude T b := by
  unfold qVFamLocalQPilotMagnitude qVFamTensorCoefficient
  have horder : (0 : Real) ≤ ((qVFamily T b).order : Real) := by positivity
  have hp : (1 : Real) < (qVFamTensorP T b : Real) :=
    by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt
  exact mul_nonneg horder (Real.log_pos hp).le

theorem rootThetaMagnitudeValue_eq (j : SignedLabel l.value) :
    rootThetaMagnitudeValue T b j =
      qVFamLocalQPilotMagnitude T b *
        (((gaussExponent j.1).toNat : Real) / (2 * (l.value : Real))) := by
  unfold rootThetaMagnitudeValue qVFamLocalQPilotMagnitude
    qVFamTensorCoefficient qVFamPaperThetaTensorCoefficient qVFamPaperRootCoefficient
  simp only [qVFamTensorV, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  norm_num
  ring

theorem rootThetaMagnitudeAverage_eq_qVFamCoefficient_mul_coefficient :
    (rootThetaMagnitudeProcession T b).average =
      qVFamLocalQPilotMagnitude T b *
        rootThetaAverageCoefficient (l := l) := by
  unfold WeightedValues.average rootThetaMagnitudeProcession
    rootThetaAverageCoefficient
  rw [div_one]
  calc
    ∑ j : SignedLabel l.value,
        (Fintype.card (SignedLabel l.value) : Real)⁻¹ *
          rootThetaMagnitudeValue T b j =
      ∑ j : SignedLabel l.value,
        (Fintype.card (SignedLabel l.value) : Real)⁻¹ *
          (qVFamLocalQPilotMagnitude T b *
            (((gaussExponent j.1).toNat : Real) / (2 * (l.value : Real)))) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [rootThetaMagnitudeValue_eq]
    _ = qVFamLocalQPilotMagnitude T b *
          ((∑ j : SignedLabel l.value,
              ((gaussExponent j.1).toNat : Real)) /
            (2 * (l.value : Real) *
              (Fintype.card (SignedLabel l.value) : Real))) := by
        have hterm : ∀ j : SignedLabel l.value,
            (Fintype.card (SignedLabel l.value) : Real)⁻¹ *
              (qVFamLocalQPilotMagnitude T b *
                (((gaussExponent j.1).toNat : Real) / (2 * (l.value : Real)))) =
            ((Fintype.card (SignedLabel l.value) : Real)⁻¹ *
              qVFamLocalQPilotMagnitude T b) *
                (((gaussExponent j.1).toNat : Real) / (2 * (l.value : Real))) := by
          intro j
          ring
        rw [Finset.sum_congr rfl (fun j _ => hterm j)]
        rw [← Finset.mul_sum]
        rw [Finset.sum_div]
        rw [Finset.mul_sum]
        conv_rhs => rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring

/-- Direct scalar comparison condition: the exact arithmetic coefficient of
the root theta average is at most one. -/
def DirectScalarComparisonCondition : Prop :=
  rootThetaAverageCoefficient (l := l) ≤ 1

/-- Exact minimal arithmetic inequality: if the theta coefficient is at most
one, the root theta average is at most the local q-pilot magnitude. -/
theorem rootThetaMagnitudeAverage_le_qVFamLocalQPilotMagnitude_of_coefficient
    (hcoef : rootThetaAverageCoefficient (l := l) ≤ 1) :
    (rootThetaMagnitudeProcession T b).average ≤
      qVFamLocalQPilotMagnitude T b := by
  rw [rootThetaMagnitudeAverage_eq_qVFamCoefficient_mul_coefficient]
  have hq : 0 ≤ qVFamLocalQPilotMagnitude T b :=
    qVFamLocalQPilotMagnitude_nonneg T b
  calc
    qVFamLocalQPilotMagnitude T b * rootThetaAverageCoefficient (l := l) ≤
        qVFamLocalQPilotMagnitude T b * 1 := by
      exact mul_le_mul_of_nonneg_left hcoef hq
    _ = qVFamLocalQPilotMagnitude T b := by ring

/-- Exact minimal arithmetic gap, recorded as a Prop without inhabitant. -/
def DirectScalarComparisonGap : Prop :=
  DirectScalarComparisonCondition (l := l)

end LeanFormal.IUT.XiFPaper.S679DirectScalarComparisonActual

end
