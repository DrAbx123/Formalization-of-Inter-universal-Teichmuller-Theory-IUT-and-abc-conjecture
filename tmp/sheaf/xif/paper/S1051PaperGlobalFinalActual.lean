import tmp.sheaf.xif.paper.S1050PerBQPilotCoefficientAuditActual
import tmp.sheaf.xif.paper.S1043CorrectedBridgeExactActual
import tmp.sheaf.xif.paper.S1025S994FiniteInputActual
import tmp.sheaf.xif.paper.S919GlobalWeightedInequalityActual
import tmp.sheaf.xif.PaperAssembly

/-! # S1051: final Cor312 with the PAPER global qPilot

Paper global qPilot is s1050PaperGlobalQPilotLog In = weightedPaperV(s994VR In),
not the classical globalQPilotLog and not O.qPilotLogVolume.

The comparison P.average ≤ -paperGlobal is proved directly:
  P.average = -weightedPaperV(s994VS In)      (exact hull-average identification)
  weightedPaperV(s994VR In) ≤ weightedPaperV(s994VS In)   (S994 actual)
so no classical=paper per-b equality is needed for the comparison.

The certificate uses qPilotLogVolume = paperGlobal.  Exact inputs are the
hull-average identification, the paper qParameter card, and finite links.
No classical=paper fake. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1051PaperGlobalFinalActual

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
open LeanFormal.IUT.XiFPaper.S1037GlobalQPilotAuditActual
open LeanFormal.IUT.XiFPaper.S1043CorrectedBridgeExactActual
open LeanFormal.IUT.XiFPaper.S1050PerBQPilotCoefficientAuditActual
open LeanFormal.IUT.XiFPaper.ThetaLinkFromSource
open MeasureTheory

universe uX uLabel

variable {l : PrimeGeFive}
variable {X : Type uX} {label : Type uLabel} [Fintype label] [Nonempty label]
variable (P : PaperSignedHull X label)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Exact paper qParameter card: paper global qPilot = -|log qParameter|. -/
structure S1051PaperQParameterCard (In : S994FiniteInput T) where
  qParameter : Real
  qParameter_pos : 0 < qParameter
  qParameter_log_ne_zero : Real.log qParameter ≠ 0
  qPilotLogVolume_eq :
    s1050PaperGlobalQPilotLog (l := l) T In = -|Real.log qParameter|

/-- Paper global comparison from S994 + hull-average identification. -/
theorem s1051PaperComparison
    (In : S994FiniteInput T)
    (hullavg :
      P.procession.average =
        -weightedPaperV (l := l) T (s994VS (l := l) T In)) :
    P.procession.average ≤ -s1050PaperGlobalQPilotLog (l := l) T In := by
  unfold s1050PaperGlobalQPilotLog
  rw [hullavg]
  have h := s994GlobalWeightedInequality (l := l) T In
  linarith

/-- Paper input with qPilotLogVolume = paper global. -/
noncomputable def s1051PaperXiFInput
    (In : S994FiniteInput T)
    (hullavg :
      P.procession.average =
        -weightedPaperV (l := l) T (s994VS (l := l) T In))
    (D : S1051PaperQParameterCard (l := l) T In) :
    PaperXiFInput P where
  data :=
    { thetaHullLogVolume := P.signedHullLogVolume
      qPilotLogVolume := s1050PaperGlobalQPilotLog (l := l) T In
      qPilot_mem_ray := by
        rw [mem_hullLogVolumeRay_iff, P.signedHullLogVolume_eq_neg_average]
        have h := s1051PaperComparison (l := l) P T In hullavg
        linarith
      qParameter := D.qParameter
      qParameter_pos := D.qParameter_pos
      qParameter_log_ne_zero := D.qParameter_log_ne_zero
      qPilotLogVolume_eq := D.qPilotLogVolume_eq }
  theta_eq := rfl

/-- Paper certificate. -/
noncomputable def s1051PaperCertificate
    (In : S994FiniteInput T)
    (hullavg :
      P.procession.average =
        -weightedPaperV (l := l) T (s994VS (l := l) T In))
    (D : S1051PaperQParameterCard (l := l) T In) :
    StepXIFiniteCertificateSigned label :=
  paperCertificate (I := s1051PaperXiFInput (l := l) P T In hullavg D)

/-- Final Cor312 from paper global qPilot; no classical=paper equality. -/
theorem s1051FinalCor312
    (In : S994FiniteInput T)
    (hullavg :
      P.procession.average =
        -weightedPaperV (l := l) T (s994VS (l := l) T In))
    (D : S1051PaperQParameterCard (l := l) T In)
    (links : FiniteStepXILinkEvidence
      (s1051PaperCertificate (l := l) P T In hullavg D).toStepXIFiniteCertificate) :
    Cor312Conclusion
      ((s1051PaperCertificate (l := l) P T In hullavg D).toContract
        (paperSignedLinkEvidence
          (I := s1051PaperXiFInput (l := l) P T In hullavg D) links)) :=
  paperCor312Conclusion
    (I := s1051PaperXiFInput (l := l) P T In hullavg D) links

/-- Exact minimal paper final inputs. -/
structure S1051PaperFinalInput where
  In : S994FiniteInput T
  hullavg :
    P.procession.average =
      -weightedPaperV (l := l) T (s994VS (l := l) T In)
  card : S1051PaperQParameterCard (l := l) T In
  links : FiniteStepXILinkEvidence
    (s1051PaperCertificate (l := l) P T In hullavg card).toStepXIFiniteCertificate

theorem s1051PaperFinalCor312_of_input
    (H : S1051PaperFinalInput (l := l) P T) :
    Cor312Conclusion
      ((s1051PaperCertificate (l := l) P T H.In H.hullavg H.card).toContract
        (paperSignedLinkEvidence
          (I := s1051PaperXiFInput (l := l) P T H.In H.hullavg H.card) H.links)) :=
  s1051FinalCor312 (l := l) P T H.In H.hullavg H.card H.links

end LeanFormal.IUT.XiFPaper.S1051PaperGlobalFinalActual

end
