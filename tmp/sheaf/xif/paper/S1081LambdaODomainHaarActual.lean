import tmp.sheaf.xif.paper.S1080PushforwardConstructionActual
import tmp.sheaf.xif.paper.S805NonzeroHullReplacementActual
import tmp.sheaf.xif.paper.S925HullFinitenessActual

/-! # S1081: domain finiteness/positivity for paperLambdaORegion(cRoot)

paperLambdaORegion(cRoot) is the S805 qPilotPaperRegion (rfl).
Finiteness is actual: qPilotPaperRegion ⊆ paperRootThetaHullNonzero and S925
proves the latter has finite Haar.
Positivity is not derivable from the closed-submodule structure alone; it is
kept as the exact S1080DomainPositivity input (the correct L-stalk lattice
positivity).  Then S1080 gives hull positivity/finiteness of the pushforward
measure.

No ambient rootStackHaar positivity is used. -/

noncomputable section
open scoped BigOperators TensorProduct Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1081LambdaODomainHaarActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.S925HullFinitenessActual
open LeanFormal.IUT.XiFPaper.S1073RootStackPaperThetaHullActual
open LeanFormal.IUT.XiFPaper.S1076RootStackPaperThetaHullMeasureActual
open LeanFormal.IUT.XiFPaper.S1079RootStackMeasureAuditActual
open LeanFormal.IUT.XiFPaper.S1080PushforwardConstructionActual
open LeanFormal.IUT.XiFPaper.S824RootStackyHaarVolumeActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open MeasureTheory Topology

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- paperLambdaORegion(cRoot) is exactly the S805 paper qPilot region. -/
theorem s1081LambdaO_eq_qPilotPaperRegion :
    paperLambdaORegion (l := l) T b
        (paperRootCoefficientFamily (l := l) T b) =
      qPilotPaperRegion (l := l) T b := rfl

/-- Actual finiteness of the lambda-O region under the block Haar. -/
theorem s1081DomainFiniteness_actual :
    S1080DomainFiniteness (l := l) T b := by
  unfold S1080DomainFiniteness
  rw [s1081LambdaO_eq_qPilotPaperRegion (l := l) T b]
  exact lt_of_le_of_lt
    (measure_mono (qPilotPaperRegion_subset_nonzeroHull (l := l) T b))
    (paperRootThetaHullNonzero_measure_lt_top (l := l) T b Measure.addHaar)

/-- Exact positivity input: L-stalk Haar of the lambda-O lattice. -/
def S1081DomainPositivityRequired : Prop :=
  S1080DomainPositivity (l := l) T b

/-- Hull positivity of the S1080 pushforward measure from domain positivity
plus the pushforward identity. -/
theorem s1081Hull_positivity_of_pushforward
    (heq : S1080PushforwardHullEq (l := l) T b)
    (hpos : S1081DomainPositivityRequired (l := l) T b) :
    0 < s1080PushforwardHaar (l := l) T b
      (rootStackPaperThetaHull (l := l) T b) :=
  s1080Hull_positivity_of_domain (l := l) T b heq hpos

/-- Hull finiteness of the S1080 pushforward measure: finiteness is now
actual, only the pushforward identity remains. -/
theorem s1081Hull_finiteness_of_pushforward
    (heq : S1080PushforwardHullEq (l := l) T b) :
    s1080PushforwardHaar (l := l) T b
      (rootStackPaperThetaHull (l := l) T b) < ⊤ :=
  s1080Hull_finiteness_of_domain (l := l) T b heq
    (s1081DomainFiniteness_actual (l := l) T b)

/-- Exact minimum: pushforward identity + L-stalk domain positivity. -/
def S1081ExactMinimum : Prop :=
  S1080PushforwardHullEq (l := l) T b ∧
    S1081DomainPositivityRequired (l := l) T b

end LeanFormal.IUT.XiFPaper.S1081LambdaODomainHaarActual

end
