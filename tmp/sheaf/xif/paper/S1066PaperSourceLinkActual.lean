import tmp.sheaf.xif.paper.S1051PaperGlobalFinalActual
import tmp.sheaf.xif.paper.S1057PaperGlobalQPilotLogActual
import tmp.sheaf.xif.paper.S779RootHullNonzeroFixActual

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1066PaperSourceLinkActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.S1025S994FiniteInputActual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open LeanFormal.IUT.XiFPaper.S1050PerBQPilotCoefficientAuditActual
open LeanFormal.IUT.XiFPaper.S1051PaperGlobalFinalActual
open LeanFormal.IUT.XiFPaper.S1057PaperGlobalQPilotLogActual
open LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual
open MeasureTheory

universe uX uLabel
variable {l : PrimeGeFive}
variable {X : Type uX} {label : Type uLabel} [Fintype label] [Nonempty label]
variable (P : PaperSignedHull X label)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Global paper theta hull log from the NONZERO theta image finite hull: the
weighted sum of the s994VS finite hull logs. -/
noncomputable def paperGlobalThetaHullNonzeroLog
    (In : S994FiniteInput T) : Real :=
  weightedPaperV (l := l) T (s994VS (l := l) T In)

/-- Exact hull-average input identifying the paper signed hull with the global
nonzero theta finite hull. -/
def S1066HullAverageExact (In : S994FiniteInput T) : Prop :=
  P.procession.average =
    -weightedPaperV (l := l) T (s994VS (l := l) T In)

/-- Under the hull-average input, the paper signed hull log is exactly the
global nonzero theta log. -/
theorem S1066PaperSigned_eq_nonzero
    (In : S994FiniteInput T)
    (h : S1066HullAverageExact (l := l) P T In) :
    P.signedHullLogVolume =
      paperGlobalThetaHullNonzeroLog (l := l) T In := by
  unfold paperGlobalThetaHullNonzeroLog
  rw [P.signedHullLogVolume_eq_neg_average, h]
  ring

/-- Source-link input card: paper global qPilot and nonzero theta hull. -/
structure S1066PaperSourceInput where
  In : S994FiniteInput T
  hullavg : S1066HullAverageExact (l := l) P T In
  card : S1051PaperQParameterCard (l := l) T In
  links : FiniteStepXILinkEvidence
    (s1051PaperCertificate (l := l) P T In hullavg card).toStepXIFiniteCertificate

/-- Final Cor312 with paper global qPilot and diagonal/nonzero theta hull
identified; the local paperQPilotLogVolume C3 is not used. -/
theorem s1066FinalCor312
    (H : S1066PaperSourceInput (l := l) P T) :
    Cor312Conclusion
      ((s1051PaperCertificate (l := l) P T H.In H.hullavg H.card).toContract
        (paperSignedLinkEvidence
          (I := s1051PaperXiFInput (l := l) P T H.In H.hullavg H.card) H.links)) :=
  s1051PaperFinalCor312_of_input (l := l) P T
    { In := H.In
      hullavg := H.hullavg
      card := H.card
      links := H.links }

/-- Exact source-link list. -/
def S1066ExactInputs : Prop :=
  Nonempty (S1066PaperSourceInput (l := l) P T)

end LeanFormal.IUT.XiFPaper.S1066PaperSourceLinkActual

end
