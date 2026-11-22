import tmp.sheaf.xif.paper.S1072CanonicalQ1URegionActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual

/-! # S1096: qPilot q[1u] log formula supply

NormalizedGeneratorSupplyMissing (a generator in CommonPrimeCompletion with the
normalized norm at qVFamPureCoefficient) is reduced to the exact coefficient gap
qVFamNormalizedCoefficient = qVFamPureCoefficient.  Under that gap the supply and
the qPilotQ1U log formula are actual; without it they remain exact.  This is not
an identification of the default valuation norm with the normalized spectral
norm on the qVFamily element. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1096Q1ULogSupplyActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S1072CanonicalQ1URegionActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]

/-- Exact coefficient gap: normalized coefficient equals the default norm
coefficient of the qVFamily unit. -/
def S1096CoefficientGap : Prop :=
  QVFamNormalizedCoefficientGap (l := l) T b

/-- Under the coefficient gap, the normalized generator is an actual normalized
generator supply at qVFamPureCoefficient.  The generator is the actual
qVFamily generator in CommonPrimeCompletion. -/
noncomputable def s1096Supply_of_coefficientGap
    (h : S1096CoefficientGap (l := l) T b) :
    NormalizedGeneratorSupply (l := l) T b :=
  qVFamNormalizedGeneratorSupply_of_coefficient_eq (l := l) T b h

/-- Conditional actual missing-supply witness. -/
theorem s1096SupplyMissing_of_coefficientGap
    (h : S1096CoefficientGap (l := l) T b) :
    NormalizedGeneratorSupplyMissing (l := l) T b :=
  ⟨s1096Supply_of_coefficientGap (l := l) T b h⟩

/-- Conditional actual qPilot q[1u] log formula, under the coefficient gap. -/
theorem s1096Q1ULogFormula_of_coefficientGap
    (h : S1096CoefficientGap (l := l) T b) :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b)
        qVFamTensorTuple mu (qPilotQ1URegion (l := l) T b) =
      -((∑ i : qVFamTensorV, qVFamPureCoefficient T b i) *
        Real.log (qVFamTensorP T b : Real)) :=
  qPilotQ1URegion_logVolume (l := l) T b mu
    (s1096Supply_of_coefficientGap (l := l) T b h)

/-- Exact minimal input for the supply/log formula. -/
def S1096ExactMinimal : Prop :=
  S1096CoefficientGap (l := l) T b

/-- The coefficient gap is itself exactly the unproved norm-instance
identification; it is not the default-to-normalized norm equality. -/
def S1096NormInstanceExact : Prop :=
  qVFamNormalizedCoefficient (l := l) T b = qVFamPureCoefficient (l := l) T b ()

end LeanFormal.IUT.XiFPaper.S1096Q1ULogSupplyActual
end