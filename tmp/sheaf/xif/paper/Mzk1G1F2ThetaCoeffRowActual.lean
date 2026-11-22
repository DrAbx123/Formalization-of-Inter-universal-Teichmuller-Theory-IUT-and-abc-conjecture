/- R2/R1 actual theta coefficient supply: actual qVFam rows/places + K-side theta coefficients.

  Uses the DONE alignment `thetaTensorQVFamAlignmentOfActual` (Bad-indexed coefficients
  `(gaussExponent j.1).toNat * actualRootCoeff T b ()`) and the actual K-side coefficient
  `ksThetaCoeff`, together with the actual one-factor tensor places
  `qVFamTensorPlaces T b`; this supplies the actual qVFam rows (places + coefficients)
  needed by R1/R2. No stub, no sorry/axiom. -/
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import tmp.sheaf.xif.paper.SignedLabelOneActual
import tmp.sheaf.xif.paper.Mzk1G1F2ThetaTensorQVFamAlignmentActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaCoeffRowActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaTensorQVFamAlignmentActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- **实际 theta 系数行**（`qVFamTensorV`-值），直接由实际数据给出
    （与 DONE 的 `ksThetaCoeff` 相同表达式）。 -/
noncomputable def thetaCoeffRow (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) : qVFamTensorV → ℝ :=
  fun _ => ((gaussExponent j.1).toNat : ℝ) * actualRootCoeff (l := l) T b ()

theorem thetaCoeffRow_apply (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) (i : qVFamTensorV) :
    thetaCoeffRow T b j i =
      ((gaussExponent j.1).toNat : ℝ) * actualRootCoeff (l := l) T b () := rfl

/-- 与 alignment 的 coefficients 一致（同一实际数据）。 -/
theorem thetaCoeffRow_eq_alignment (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) (i : qVFamTensorV) :
    thetaCoeffRow T b j i =
      (thetaTensorQVFamAlignmentOfActual (l := l) T).coefficients j b := rfl

/-- **实际 qVFam 行**：一个 Bad 位的 actual tensor places + actual theta 系数。 -/
structure ThetaQVFamRow (l : PrimeGeFive) (T : SourceNativeInitialThetaData.{0} l) where
  b : Bad (nativePlaceSelection T)
  places : (i : qVFamTensorV) → Unit → FinitePlaceAtPrime T.arithmetic.F (qVFamTensorP T b)
  coeff : SignedLabel l.value → qVFamTensorV → ℝ

noncomputable def thetaQVFamRowOfBad (b : Bad (nativePlaceSelection T)) :
    ThetaQVFamRow l T where
  b := b
  places := qVFamTensorPlaces T b
  coeff := thetaCoeffRow T b

theorem thetaQVFamRowOfBad_places (b : Bad (nativePlaceSelection T)) :
    (thetaQVFamRowOfBad (l := l) T b).places = qVFamTensorPlaces T b := rfl

theorem thetaQVFamRowOfBad_coeff (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) :
    (thetaQVFamRowOfBad (l := l) T b).coeff j = thetaCoeffRow T b j := rfl

#print axioms thetaCoeffRow_eq_alignment
#print axioms thetaQVFamRowOfBad_places
#print axioms thetaQVFamRowOfBad_coeff

end LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaCoeffRowActual