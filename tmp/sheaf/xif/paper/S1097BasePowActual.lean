import tmp.sheaf.xif.paper.S1089RatioActual
/-! # S1097: S1089BasePow from the rational residue base
S118 gives residueNormBase(place) = lowerBase^localResidueDegree.  The rational
lower base is the rational prime p (residue field F_p).  This file records that
identification as the exact minimum and proves S1089BasePow from it. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
namespace LeanFormal.IUT.XiFPaper.S1097BasePowActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1089RatioActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
/-- Exact rational lower-base identity: residueNormBase of the comap place is p. -/
def S1097RationalBase : Prop :=
  residueNormBase (comap (k := ℚ) (qVFamTensorPlace T b)) =
    (qVFamTensorP T b : Real)
theorem s1089BasePow_of_rationalBase
    (hbase : S1097RationalBase (l := l) T b) :
    S1089BasePow (l := l) T b := by
  unfold S1089BasePow
  rw [residueNormBase_eq_lower_pow (k := ℚ) (qVFamTensorPlace T b), hbase]
end LeanFormal.IUT.XiFPaper.S1097BasePowActual
