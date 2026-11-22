import tmp.sheaf.xif.paper.S509OddLiftChoiceActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S542ThetaQHalfActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S485TateTwoTorsionQSqrtActual
open LeanFormal.IUT.XiFPaper.S509OddLiftChoiceActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

def qHalfUnitOfTheta (thetaUnit : (ACF T b)ˣ) : (ACF T b)ˣ :=
  thetaUnit ^ l.value

theorem qHalfUnitOfTheta_sq (thetaUnit : (ACF T b)ˣ)
    (h : thetaUnit ^ (2 * l.value) = qUnit T b) :
    qHalfUnitOfTheta (l := l) T b thetaUnit ^ 2 = qUnit T b := by
  unfold qHalfUnitOfTheta
  rw [pow_two, ← pow_add]
  rw [show l.value + l.value = 2 * l.value by ring, h]

/-- Correct μ_{2l} action on the q-half: multiply by ζ^l, not ζ. -/
def muTwoLAction (zeta : (ACF T b)ˣ) (qHalf : (ACF T b)ˣ) : (ACF T b)ˣ :=
  zeta ^ l.value * qHalf

theorem muTwoLAction_sq (zeta qHalf : (ACF T b)ˣ)
    (hzeta : zeta ^ (2 * l.value) = 1)
    (hq : qHalf ^ 2 = qUnit T b) :
    muTwoLAction (l := l) T b zeta qHalf ^ 2 = qUnit T b := by
  unfold muTwoLAction
  rw [mul_pow, hq, pow_two, ← pow_add]
  rw [show l.value + l.value = 2 * l.value by ring, hzeta, one_mul]

end LeanFormal.IUT.XiFPaper.S542ThetaQHalfActual
end