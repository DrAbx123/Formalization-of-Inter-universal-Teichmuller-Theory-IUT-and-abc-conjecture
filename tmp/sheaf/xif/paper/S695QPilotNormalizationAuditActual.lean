import tmp.sheaf.xif.paper.BadPlacePaperRootComparisonActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual

/-! # S695: qPilot normalization audit

Paper q-pilot coefficient = classical ord_v(q_v)/(2l) (q[2u] normalization).
The classical tensor coefficient qVFamTensorCoefficient = order; qPilot divides it by 2l.
`qVFamTensorCoefficient = order(qVFamily)`, which is exactly the paper qPilot
coefficient.  `qVFamPaperThetaTensorCoefficient j = j^2 * order/(2l)` is the
paper Theta root coefficient.  The stale j-dependent old coefficient
`QVFamTensorFractionalActual.qVFamTensorCoefficient` is order*degree*j^2 and is
missing the 1/(2l) root normalization; it must not be used as the paper Theta
coefficient.  At l=29, j=8 gives j^2/(2l)=64/58>1, so positive coefficients
can exceed the qPilot coefficient; this is not a qPilot normalization error. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S695QPilotNormalizationAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Classical qVFamily coefficient: order(q_v). -/
theorem qVFamTensorCoefficient_eq_order :
    qVFamTensorCoefficient T b = ((QPilotZeroLocusDivisorActual.qVFamily T b).order : Real) := rfl

/-- Paper q-pilot coefficient: classical order/(2l). -/
theorem qPilotCoefficient_eq_classical_div_twoL :
    qVFamTensorCoefficient T b / (2 * (l.value : Real)) =
      ((QPilotZeroLocusDivisorActual.qVFamily T b).order : Real) /
        (2 * (l.value : Real)) := by
  rw [qVFamTensorCoefficient_eq_order]

/-- The paper root Theta coefficient is j^2 * order/(2l). -/
theorem qVFamPaperThetaTensorCoefficient_eq :
    ∀ j : SignedLabel l.value,
      qVFamPaperThetaTensorCoefficient T b j =
        ((gaussExponent j.1).toNat : Real) *
          (((QPilotZeroLocusDivisorActual.qVFamily T b).order : Real) / (2 * l.value : Real)) := by
  intro j
  unfold qVFamPaperThetaTensorCoefficient qVFamPaperRootCoefficient
  ring_nf

/-- The l=29, j=8 ratio is 64/58 > 1: the Theta coefficient can exceed the
qPilot coefficient without any qPilot normalization error. -/
theorem l29_j8_ratio_gt_one :
    (1 : Real) < ((8 : Real) ^ 2) / (2 * 29 : Real) := by
  norm_num

/-- l=29 is at least five and is prime. -/
theorem l29_prime_and_ge_five :
    Nat.Prime 29 ∧ 5 ≤ 29 := by
  norm_num

end LeanFormal.IUT.XiFPaper.S695QPilotNormalizationAuditActual

end
