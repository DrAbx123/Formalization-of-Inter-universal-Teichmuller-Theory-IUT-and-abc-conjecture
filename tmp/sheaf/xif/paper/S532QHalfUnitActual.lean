import tmp.sheaf.xif.paper.S530EtThQSqrtRecipeSpecActual
import tmp.sheaf.xif.paper.S485TateTwoTorsionQSqrtActual
import tmp.sheaf.xif.paper.S509OddLiftChoiceActual
/-! # S532: actual qHalfUnit = thetaUnit^l from the algebraic closure
Construct an actual 2l-th root thetaUnit of qUnit in ACF, set
qHalfUnit = thetaUnit^l; prove thetaUnit^(2l)=qUnit, qHalfUnit^2=qUnit,
and the mu_{2l} ambiguity.  The EtTh evaluation/special-point section is
recorded as exact missing (S530). -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S532QHalfUnitActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S485TateTwoTorsionQSqrtActual
open LeanFormal.IUT.XiFPaper.S509OddLiftChoiceActual
open LeanFormal.IUT.XiFPaper.S530EtThQSqrtRecipeSpecActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
noncomputable def thetaRootElement : ACF T b :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (qUnit T b : ACF T b)
    (by
      have h : 0 < 2 * l.value := Nat.mul_pos (by norm_num) l.prime.pos
      exact h))
theorem thetaRootElement_pow :
    thetaRootElement T b ^ (2 * l.value) = (qUnit T b : ACF T b) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (qUnit T b : ACF T b)
    (by
      have h : 0 < 2 * l.value := Nat.mul_pos (by norm_num) l.prime.pos
      exact h))
theorem thetaRootElement_ne_zero : thetaRootElement T b ≠ 0 := by
  intro h
  have hpow := thetaRootElement_pow T b
  rw [h, zero_pow (Nat.mul_ne_zero (by norm_num) l.prime.ne_zero)] at hpow
  exact (Units.ne_zero (qUnit T b)) hpow.symm
noncomputable def thetaUnitActual : (ACF T b)ˣ :=
  Units.mk0 (thetaRootElement T b) (thetaRootElement_ne_zero T b)
theorem thetaUnitActual_pow :
    thetaUnitActual T b ^ (2 * l.value) = qUnit T b := by
  ext
  simpa [thetaUnitActual] using thetaRootElement_pow T b
noncomputable def qHalfUnitActual : (ACF T b)ˣ :=
  thetaUnitActual T b ^ l.value
theorem qHalfUnitActual_sq : qHalfUnitActual T b ^ 2 = qUnit T b := by
  unfold qHalfUnitActual
  rw [← pow_mul, Nat.mul_comm l.value 2]
  exact thetaUnitActual_pow T b
theorem qHalfUnitActual_eq_theta_pow :
    qHalfUnitActual T b = thetaUnitActual T b ^ l.value := rfl
/-- Actual qHalf data with the square and the theta^(2l) relation. -/
structure QHalfUnitActualData where
  thetaUnit : (ACF T b)ˣ
  theta_pow : thetaUnit ^ (2 * l.value) = qUnit T b
  qHalfUnit : (ACF T b)ˣ
  qHalf_eq : qHalfUnit = thetaUnit ^ l.value
  qHalf_sq : qHalfUnit ^ 2 = qUnit T b
noncomputable def qHalfUnitActualData : QHalfUnitActualData T b where
  thetaUnit := thetaUnitActual T b
  theta_pow := thetaUnitActual_pow T b
  qHalfUnit := qHalfUnitActual T b
  qHalf_eq := qHalfUnitActual_eq_theta_pow T b
  qHalf_sq := qHalfUnitActual_sq T b
/-- The ratio with the chosen q-sqrt root is a mu_2 element. -/
noncomputable def qHalfMuTwoRatio : (ACF T b)ˣ :=
  qHalfUnitActual T b * (qHalfRootUnit T b)⁻¹
theorem qHalfMuTwoRatio_sq : qHalfMuTwoRatio T b ^ 2 = 1 := by
  unfold qHalfMuTwoRatio
  rw [mul_pow, qHalfUnitActual_sq T b]
  rw [show (qHalfRootUnit T b)⁻¹ ^ 2 = (qUnit T b)⁻¹ by
    rw [inv_pow, qHalfRootUnit_sq T b]]
  exact mul_inv_cancel (qUnit T b)
/-- Exact missing EtTh evaluation/special-point section (S530 recipe). -/
def EtThEvaluationSplittingSectionRequired : Prop :=
  Nonempty (EtThThetaSplittingRecipe T b)
end LeanFormal.IUT.XiFPaper.S532QHalfUnitActual
