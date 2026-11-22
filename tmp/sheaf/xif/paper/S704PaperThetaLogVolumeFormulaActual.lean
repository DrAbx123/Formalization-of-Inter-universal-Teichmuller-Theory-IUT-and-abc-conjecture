import tmp.sheaf.xif.paper.S694ThetaAverageNormalizationActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual

/-! # S704: paper theta/q-pilot log-volume formulas

Source formulas used:
* IUT II Remark 4.7.3: weight 1/l* at each of the l* classes in F_l^⋇.
* IUT I Example 3.2(iv): Theta_j = q[2u]^(j^2) = q[1u]^(j^2/(2l)).
* IUT III Theorem B / Cor 3.12: average over j in F_l^⋇; q-pilot is the
  zero locus of q_v, with the native bad-place local weights.

The definitions below are the exact *linear coefficient model*.  The final
proposition records the arithmetic inequality that this model would require;
it is NOT asserted, and in fact fails for l >= 29 (coefficient (l+1)/24). -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S704PaperThetaLogVolumeFormulaActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S694ThetaAverageNormalizationActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The 2l-th-root exponent j^2/(2l) at paper label j. -/
noncomputable def paperThetaExponent (j : PaperThetaLabel l) : Real :=
  ((j.1 + 1 : Real) ^ 2) / (2 * (l.value : Real))

/-- The linear paper theta coefficient: (1/l*) sum_j j^2/(2l). -/
noncomputable def paperThetaLinearCoefficient (l : PrimeGeFive) : Real :=
  paperThetaLabelWeight l *
    ∑ j : PaperThetaLabel l, paperThetaExponent (l := l) j

/-- Per-b paper theta log magnitude in the linear coefficient model. -/
noncomputable def paperThetaLocalLog (b : Bad (nativePlaceSelection T)) : Real :=
  paperThetaLabelWeight l *
    ∑ j : PaperThetaLabel l,
      (paperThetaExponent (l := l) j *
        ((qVFamily T b).order : Real) * Real.log (qVFamTensorP T b : Real))

/-- Global theta log magnitude with native bad-place local weights. -/
noncomputable def paperThetaGlobalLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * paperThetaLocalLog T b

/-- Global q-pilot log magnitude: weighted order(q_v) log p_v. -/
noncomputable def paperQPilotGlobalLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b *
      (((qVFamily T b).order : Real) * Real.log (qVFamTensorP T b : Real))

/-- The exact arithmetic inequality required by the linear model:
average paper theta log <= q-pilot log, assuming q-pilot log positive. -/
def PaperThetaQpilotArithmeticInequality (l : PrimeGeFive) : Prop :=
  paperThetaLinearCoefficient l ≤ 1

/-- The linear theta coefficient factorizes out of the global scalar. -/
theorem paperThetaGlobalLog_eq_coefficient_mul_qPilot :
    paperThetaGlobalLog T =
      paperThetaLinearCoefficient l * paperQPilotGlobalLog T := by
  unfold paperThetaGlobalLog paperThetaLocalLog paperThetaLinearCoefficient
    paperQPilotGlobalLog
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The exact global comparison in the linear model. -/
def PaperThetaGlobalComparison : Prop :=
  paperThetaGlobalLog T ≤ paperQPilotGlobalLog T

/-- Conditional equivalence: the global comparison is exactly the arithmetic
coefficient inequality when the q-pilot scalar is positive. -/
theorem paperThetaGlobalComparison_iff_coefficient
    (hq : 0 < paperQPilotGlobalLog T) :
    PaperThetaGlobalComparison T ↔ PaperThetaQpilotArithmeticInequality l := by
  unfold PaperThetaGlobalComparison PaperThetaQpilotArithmeticInequality
  rw [paperThetaGlobalLog_eq_coefficient_mul_qPilot]
  constructor
  · intro h
    have h' : paperThetaLinearCoefficient l * paperQPilotGlobalLog T ≤
        1 * paperQPilotGlobalLog T := by simpa using h
    exact le_of_mul_le_mul_right h' hq
  · intro h
    simpa using mul_le_mul_of_nonneg_right h hq.le

end LeanFormal.IUT.XiFPaper.S704PaperThetaLogVolumeFormulaActual
end