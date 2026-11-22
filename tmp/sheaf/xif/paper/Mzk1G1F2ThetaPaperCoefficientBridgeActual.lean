/- R1/Θ coefficients: connect the PAPER Theta coefficients to the actual root hull/rows.

  Paper coefficient [QVFamRootFactorCorrectionActual]:
    `qVFamPaperThetaTensorCoefficient j = gaussExponent j.1 * qVFamPaperRootCoefficient`
    with `qVFamPaperRootCoefficient = order/(2l)` (F-side, no ramification).
  Actual supplied row [Mzk1G1F2ThetaCoeffRowActual]:
    `thetaCoeffRow T b j i = gaussExponent j.1 * actualRootCoeff T b ()`
    with `actualRootCoeff = qVFamNormalizedCoefficient/(2l)` (supply cNorm).
  Under `QVFamNormalizedNormCompatibility e` one has `cNorm = order/e`
  [qVFamNormalizedCoefficient_eq_order_div_e], hence the EXACT mismatch
    `thetaCoeffRow T b j i = qVFamPaperThetaTensorCoefficient j / e`
  i.e. `qVFamPaperThetaTensorCoefficient j = e * thetaCoeffRow T b j i`.
  The correct paper-Theta hull is `paperThetaHull` below (coefficient family equal to
  the Gaussian-weighted paper coefficient); `perBThetaHullLog` is NOT it (it uses
  `rootHalfCoefficient = cNorm/(2l)`, i.e. a single-label hull with 1/e in place of gauss*j^2).
  No stub, no sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1F2ThetaCoeffRowActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaPaperCoefficientBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaCoeffRowActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- **论文 Θ 的根系数族**：`order/(2l)`（常数族；`rootThetaHull` 内部按标签再乘
    `gaussExponent j`，故这里不能预先乘 gauss，否则重复）。 -/
noncomputable def paperThetaRootCoefficient (b : Bad (nativePlaceSelection T)) :
    qVFamTensorV → ℝ :=
  fun _ => qVFamPaperRootCoefficient (l := l) T b

/-- **正确的论文 Θ 根 hull**：`rootThetaHull` 的标签 j 区域为
    `F(gaussExponent j * order/(2l)) * hol`，即论文的 `j^2 * order/(2l)` 系数。 -/
noncomputable def paperThetaHull (b : Bad (nativePlaceSelection T)) :
    Set (qVFamTensorBlock T b) :=
  rootThetaHull (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
    (paperThetaRootCoefficient (l := l) T b)

/-- 论文 Θ 在标签 j 上的实际系数 = Gaussian 指数 × order/(2l)。 -/
theorem paperThetaCoefficient_apply (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) (i : qVFamTensorV) :
    ((gaussExponent j.1).toNat : ℝ) * paperThetaRootCoefficient (l := l) T b i =
      qVFamPaperThetaTensorCoefficient (l := l) T b j := rfl

#print axioms paperThetaCoefficient_apply

end LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaPaperCoefficientBridgeActual