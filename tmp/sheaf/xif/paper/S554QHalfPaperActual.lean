import tmp.sheaf.xif.paper.S551QHalfComparisonActual
import tmp.sheaf.xif.paper.S542ThetaQHalfActual

/-! # S554: actual paper qHalf package

From S551 comparison data and S542 theta/qHalf actions: thetaUnit^(2l)=qUnit,
qHalf=thetaUnit^l, qHalf^2=qUnit, mu_{2l} acts by zeta^l, and the ratio with
S546 qHalfRoot is in mu_{2l}.  All equalities are derived, not assumed.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S554QHalfPaperActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S551QHalfComparisonActual
open LeanFormal.IUT.XiFPaper.S542ThetaQHalfActual
open LeanFormal.IUT.XiFPaper.S485TateTwoTorsionQSqrtActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Actual paper qHalf package. -/
structure QHalfPaperData where
  thetaUnit : (ACF T b)ˣ
  qUnit : (ACF T b)ˣ
  qHalf : (ACF T b)ˣ
  qHalfRoot : (ACF T b)ˣ
  ratio : (ACF T b)ˣ
  theta_pow : thetaUnit ^ (2 * l.value) = qUnit
  qHalf_eq : qHalf = thetaUnit ^ l.value
  qHalf_sq : qHalf ^ 2 = qUnit
  muTwoLAction_eq :
    ∀ (zeta : (ACF T b)ˣ), zeta ^ (2 * l.value) = 1 →
      muTwoLAction (l := l) T b zeta qHalf = zeta ^ l.value * qHalf
  qHalfRoot_pow : qHalfRoot ^ (2 * l.value) = qUnit
  ratio_eq : ratio = thetaUnit / qHalfRoot
  ratio_mem_mu : ratio ∈ rootsOfUnity (2 * l.value) (ACF T b)

/-- Construct the paper package from S551 comparison data. -/
noncomputable def qHalfPaperDataOfComparison
    (C : QHalfComparisonData T b) : QHalfPaperData T b where
  thetaUnit := C.thetaUnit
  qUnit := qUnit T b
  qHalf := qHalfUnitOfTheta (l := l) T b C.thetaUnit
  qHalfRoot := C.qHalfRoot
  ratio := C.ratio
  theta_pow := C.theta_pow
  qHalf_eq := rfl
  qHalf_sq := qHalfUnitOfTheta_sq (l := l) T b C.thetaUnit C.theta_pow
  muTwoLAction_eq := by
    intro zeta hzeta
    rfl
  qHalfRoot_pow := C.qHalfRoot_pow
  ratio_eq := C.ratio_eq
  ratio_mem_mu := C.ratio_mem_mu

/-- The actual package from the actual S551 comparison data. -/
noncomputable def qHalfPaperData : QHalfPaperData T b :=
  qHalfPaperDataOfComparison (l := l) T b (qHalfComparisonData (l := l) T b)

end LeanFormal.IUT.XiFPaper.S554QHalfPaperActual
end
