import tmp.sheaf.xif.paper.S914PaperLVExInstantiationActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S918InequalityActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S914PaperLVExInstantiationActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]

/-- Actual containment R ⊆ S from S914 (no equality). -/
theorem R_subset_S : s914R (l := l) T b ⊆ s914S (l := l) T b :=
  s914R_subset_S (l := l) T b

/-- Exact positivity gap for R. -/
def S918PositivityGap : Prop :=
  0 < mu (s914R (l := l) T b)

/-- Exact finiteness gap for S. -/
def S918FinitenessGap : Prop :=
  mu (s914S (l := l) T b) < ⊤

/-- The only analytic inputs: positivity of R and finiteness of S. -/
def S918AnalyticGaps : Prop :=
  S918PositivityGap (l := l) T b mu ∧ S918FinitenessGap (l := l) T b mu

/-- Log-volume inequality V(R) ≤ V(S), conditional on the two analytic gaps. -/
theorem V_R_le_V_S_of_gaps
    (hpos : S918PositivityGap (l := l) T b mu)
    (hfin : S918FinitenessGap (l := l) T b mu) :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (s914R (l := l) T b) ≤
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (s914S (l := l) T b) :=
  s914MuLogComparison (l := l) T b mu hpos hfin

/-- Exact minimal analytic gap: positivity/finiteness only, no equality. -/
def S918ExactMinimalGap : Prop :=
  S918AnalyticGaps (l := l) T b mu

end LeanFormal.IUT.XiFPaper.S918InequalityActual
end