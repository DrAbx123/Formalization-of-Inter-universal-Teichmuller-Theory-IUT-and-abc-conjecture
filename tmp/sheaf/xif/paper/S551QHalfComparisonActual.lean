import tmp.sheaf.xif.paper.S532QHalfUnitActual
import tmp.sheaf.xif.paper.S546QHalfCandidateActual
import tmp.sheaf.xif.paper.S485TateTwoTorsionQSqrtActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S551QHalfComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S532QHalfUnitActual
open LeanFormal.IUT.XiFPaper.S546QHalfCandidateActual
open LeanFormal.IUT.XiFPaper.S485TateTwoTorsionQSqrtActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The S546 qHalfRoot specialized to the actual F-side qVFamily parameter. -/
noncomputable def qHalfRootActual : (ACF T b)ˣ :=
  qHalfRoot (l := l) (K := T.arithmetic.F) (place := FPlace T b) (qVFamily T b)

/-- Comparison data between S532 thetaUnitActual and S546 qHalfRootActual. -/
structure QHalfComparisonData where
  thetaUnit : (ACF T b)ˣ
  qHalfRoot : (ACF T b)ˣ
  theta_pow : thetaUnit ^ (2 * l.value) = qUnit T b
  qHalfRoot_pow : qHalfRoot ^ (2 * l.value) = qUnit T b
  ratio : (ACF T b)ˣ
  ratio_eq : ratio = thetaUnit / qHalfRoot
  ratio_mem_mu : ratio ∈ rootsOfUnity (2 * l.value) (ACF T b)

noncomputable def qHalfComparisonData : QHalfComparisonData T b where
  thetaUnit := thetaUnitActual T b
  qHalfRoot := qHalfRootActual T b
  theta_pow := thetaUnitActual_pow T b
  qHalfRoot_pow := by
    simpa [qHalfRootActual, qUnit] using
      qHalfRoot_pow (l := l) (K := T.arithmetic.F) (place := FPlace T b)
        (qVFamily T b)
  ratio := thetaUnitActual T b / qHalfRootActual T b
  ratio_eq := rfl
  ratio_mem_mu := by
    apply qHalfRoot_ratio_mem_rootsOfUnity (l := l)
      (K := T.arithmetic.F) (place := FPlace T b) (parameter := qVFamily T b)
    · simpa [qUnit] using thetaUnitActual_pow T b
    · simpa [qHalfRootActual, qUnit] using
        qHalfRoot_pow (l := l) (K := T.arithmetic.F) (place := FPlace T b)
          (qVFamily T b)

/-- Exact mismatch for S532 qHalfUnitActual itself: it is a square root of
qUnit, not a 2l-th root, so the mu_2l ratio theorem does not apply to it. -/
def S532QHalfUnitVs2LRootGap : Prop := (qHalfUnitActual T b) ^ 2 = qUnit T b

theorem S532QHalfUnitVs2LRootGap_holds : S532QHalfUnitVs2LRootGap T b := by
  unfold S532QHalfUnitVs2LRootGap
  exact qHalfUnitActual_sq T b

theorem l_value_ne_one : l.value ≠ 1 := by
  have h := l.ge_five
  omega

end LeanFormal.IUT.XiFPaper.S551QHalfComparisonActual

end
