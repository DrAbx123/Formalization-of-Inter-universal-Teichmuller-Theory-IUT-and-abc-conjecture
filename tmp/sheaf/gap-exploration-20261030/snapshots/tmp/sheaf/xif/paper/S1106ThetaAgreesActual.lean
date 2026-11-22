import tmp.sheaf.xif.paper.S1095PushforwardHullEqActual
import tmp.sheaf.xif.paper.S1093PaperAssemblyActual

noncomputable section
open scoped BigOperators TensorProduct Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1106ThetaAgreesActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S1073RootStackPaperThetaHullActual
open LeanFormal.IUT.XiFPaper.S1080PushforwardConstructionActual
open LeanFormal.IUT.XiFPaper.S1085PushforwardHullEqActual
open LeanFormal.IUT.XiFPaper.S1095PushforwardHullEqActual
open LeanFormal.IUT.XiFPaper.S1093PaperAssemblyActual
open MeasureTheory Topology

universe uX uLabel u
variable {l : PrimeGeFive}
variable {X : Type uX} {label : Type uLabel} [Fintype label] [Nonempty label]
variable (P : PaperSignedHull X label)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Log of the actual S1079 pushforward/L-stalk measure on the paper hull. -/
noncomputable def pushforwardThetaHullLog : Real :=
  Real.log ((s1080PushforwardHaar (l := l) T b
    (rootStackPaperThetaHull (l := l) T b)).toReal)

/-- Under the S1095 measurability inputs, the pushforward hull log is the log
of the domain lambda-O Haar. -/
theorem pushforwardThetaHullLog_eq_domainLog
    (h : S1095ExactMinimum (l := l) T b) :
    pushforwardThetaHullLog (l := l) T b =
      Real.log (((Measure.addHaar : Measure (qVFamTensorBlock T b))
        (paperLambdaORegion (l := l) T b
          (paperRootCoefficientFamily (l := l) T b))).toReal) := by
  unfold pushforwardThetaHullLog
  rw [s1095HullMeasure_eq_domainHaar (l := l) T b h]

/-- Exact identification of the ambient S782 rootStackHaar log with the
pushforward log.  S1080 records that the ambient stacky Haar is not the L-stalk
pushforward; this is a genuine exact measure identity, not a definition. -/
def S1106AmbientEqPushforward : Prop :=
  rootStackPaperThetaHullLog (l := l) T b =
    pushforwardThetaHullLog (l := l) T b

/-- Exact identification of the pushforward/domain log with the paper signed
hull scalar. -/
def S1106DomainLogEqPaper : Prop :=
  Real.log (((Measure.addHaar : Measure (qVFamTensorBlock T b))
      (paperLambdaORegion (l := l) T b
        (paperRootCoefficientFamily (l := l) T b))).toReal) =
    P.signedHullLogVolume

/-- theta_agrees from the exact pushforward/domain/paper identification. -/
theorem S1106ThetaAgrees_of_exact
    (h10 : S1095ExactMinimum (l := l) T b)
    (hAmb : S1106AmbientEqPushforward (l := l) T b)
    (hPaper : S1106DomainLogEqPaper (l := l) P T b) :
    rootStackPaperThetaHullLog (l := l) T b = P.signedHullLogVolume := by
  rw [hAmb]
  rw [pushforwardThetaHullLog_eq_domainLog (l := l) T b h10]
  exact hPaper

/-- Exact minimal data for S1106 theta_agrees. -/
def S1106ExactMinimum : Prop :=
  S1095ExactMinimum (l := l) T b ∧
    S1106AmbientEqPushforward (l := l) T b ∧
      S1106DomainLogEqPaper (l := l) P T b

theorem S1106ThetaAgrees_of_minimum
    (h : S1106ExactMinimum (l := l) P T b) :
    rootStackPaperThetaHullLog (l := l) T b = P.signedHullLogVolume :=
  S1106ThetaAgrees_of_exact (l := l) P T b h.1 h.2.1 h.2.2

end LeanFormal.IUT.XiFPaper.S1106ThetaAgreesActual

end
