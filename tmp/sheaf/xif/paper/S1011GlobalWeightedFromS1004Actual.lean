import tmp.sheaf.xif.paper.S1004QVFamFiniteLinearizationActual

noncomputable section
open scoped BigOperators TensorProduct Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S1011GlobalWeightedFromS1004Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1004QVFamFiniteLinearizationActual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Per-b qVFam finite log of the qPilot image. -/
noncomputable def s1011VR (b : Bad (nativePlaceSelection T)) : Real :=
  Real.log ((s1004H (l := l) T b).measure
    (s1004QPilotImage (l := l) T b)).toReal

/-- Per-b qVFam finite log of the paper hull image. -/
noncomputable def s1011VS (b : Bad (nativePlaceSelection T)) : Real :=
  Real.log ((s1004H (l := l) T b).measure
    (s1004Hull (l := l) T b)).toReal

/-- Global weighted inequality from S1004 per-b comparison and S919 weighted
monotonicity. -/
theorem s1011GlobalWeighted
    (hpos : ∀ b : Bad (nativePlaceSelection T),
      0 < (s1004H (l := l) T b).measure (s1004QPilotImage (l := l) T b))
    (hfin : ∀ b : Bad (nativePlaceSelection T),
      (s1004H (l := l) T b).measure (s1004Hull (l := l) T b) < ⊤) :
    weightedPaperV (l := l) T (s1011VR (l := l) T) ≤
      weightedPaperV (l := l) T (s1011VS (l := l) T) :=
  weightedPaperV_mono (l := l) T (fun b =>
    s1004PerB (l := l) T b (hpos b) (hfin b))

/-- Exact side conditions: per-b positivity/finiteness for the S1004 finite
qVFam Haar.  No scaling data or equality is used. -/
def S1011SideConditions : Prop :=
  (∀ b : Bad (nativePlaceSelection T),
    0 < (s1004H (l := l) T b).measure (s1004QPilotImage (l := l) T b)) ∧
    (∀ b : Bad (nativePlaceSelection T),
      (s1004H (l := l) T b).measure (s1004Hull (l := l) T b) < ⊤)

theorem s1011GlobalWeighted_of_side
    (h : S1011SideConditions (l := l) T) :
    weightedPaperV (l := l) T (s1011VR (l := l) T) ≤
      weightedPaperV (l := l) T (s1011VS (l := l) T) :=
  s1011GlobalWeighted (l := l) T h.1 h.2

end LeanFormal.IUT.XiFPaper.S1011GlobalWeightedFromS1004Actual

end
