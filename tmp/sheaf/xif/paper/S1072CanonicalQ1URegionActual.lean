import tmp.sheaf.xif.paper.QVFamPureFractionalScalingDataGapActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual

/-! # S1072: canonical qPilot q[1u] region from qVFamPureCoefficient

Uses the gap-file canonical pure coefficient c = -logb_p ||qVFamily|| and the
actual pure fractional scaling data obtained from an explicit normalized
generator supply.  Region = F(c)*O.  The log formula and positivity of the
coefficient are actual; the supply is the exact missing generator input. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1072CanonicalQ1URegionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]
variable (mu : Measure (qVFamTensorBlock T b))
variable [Measure.IsAddHaarMeasure mu]

/-- Canonical qPilot q[1u] region: F(qVFamPureCoefficient) * O_hol. -/
noncomputable def qPilotQ1URegion : Set (qVFamTensorBlock T b) :=
  ((arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple (qVFamPureCoefficient T b) *
    arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple : Submodule ℤ_[(qVFamTensorP T b)]
        (qVFamTensorBlock T b)) : Set (qVFamTensorBlock T b))

/-- The canonical q[1u] coefficient is positive: the qVFamily unit contracts. -/
theorem qVFamPureCoefficient_pos :
    0 < qVFamPureCoefficient T b () := by
  have hnorm_pos : 0 < ‖(qVFamDefaultCompletionUnit T b :
      Completion ((nativeBadLift T).lift b))‖ :=
    norm_pos_iff.mpr (qVFamDefaultCompletionUnit T b).ne_zero
  have hnorm_lt : ‖(qVFamDefaultCompletionUnit T b :
      Completion ((nativeBadLift T).lift b))‖ < 1 := by
    simpa [qVFamDefaultCompletionUnit] using qNorm_lt_one (qVFamily T b)
  have hp1 : (1 : Real) < (qVFamTensorP T b : Real) := by
    have hprime : Nat.Prime (qVFamTensorP T b) := Fact.out
    exact_mod_cast hprime.one_lt
  unfold qVFamPureCoefficient
  rw [neg_pos]
  exact Real.logb_neg (b := (qVFamTensorP T b : Real)) hp1 hnorm_pos hnorm_lt

/-- Actual log formula for the canonical region, conditional on the exact
normalized generator supply. -/
theorem qPilotQ1URegion_logVolume
    (S : NormalizedGeneratorSupply T b) :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b)
        qVFamTensorTuple mu (qPilotQ1URegion (l := l) T b) =
      -((∑ i : qVFamTensorV, qVFamPureCoefficient T b i) *
        Real.log (qVFamTensorP T b : Real)) :=
  arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (qVFamPureFractionalScalingData_of_supply (l := l) T b S)

/-- Per-b signed qPilot log is negative, conditional on the supply. -/
theorem qPilotQ1ULog_neg
    (S : NormalizedGeneratorSupply T b) :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b)
        qVFamTensorTuple mu (qPilotQ1URegion (l := l) T b) < 0 := by
  rw [qPilotQ1URegion_logVolume (l := l) T b mu S]
  have hc : 0 < qVFamPureCoefficient T b () :=
    qVFamPureCoefficient_pos (l := l) T b
  have hp : 1 < (qVFamTensorP T b : Real) := by
    have hprime : Nat.Prime (qVFamTensorP T b) := Fact.out
    exact_mod_cast hprime.one_lt
  have hlog : 0 < Real.log (qVFamTensorP T b : Real) := Real.log_pos hp
  have hsum : 0 < (∑ i : qVFamTensorV, qVFamPureCoefficient T b i) := by
    simpa using hc
  have hprod : 0 < (∑ i : qVFamTensorV, qVFamPureCoefficient T b i) *
      Real.log (qVFamTensorP T b : Real) := mul_pos hsum hlog
  nlinarith

/-- Per-b positivity of the qPilot magnitude. -/
theorem qPilotQ1ULogMagnitude_pos
    (S : NormalizedGeneratorSupply T b) :
    0 < -(arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b)
        qVFamTensorTuple mu (qPilotQ1URegion (l := l) T b)) :=
  neg_pos.mpr (qPilotQ1ULog_neg (l := l) T b mu S)

/-- Exact missing generator supply. -/
def S1072NormalizedSupplyRequired : Prop :=
  NormalizedGeneratorSupplyMissing (l := l) T b

end LeanFormal.IUT.XiFPaper.S1072CanonicalQ1URegionActual
end
