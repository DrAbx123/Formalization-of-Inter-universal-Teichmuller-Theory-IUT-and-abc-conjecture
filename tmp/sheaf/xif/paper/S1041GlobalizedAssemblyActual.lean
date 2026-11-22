import tmp.sheaf.xif.paper.S1040GlobalSourceLinkActual
import tmp.sheaf.xif.paper.S1038GlobalSourceQFinalActual
import tmp.sheaf.xif.PaperAssembly

/-! # S1041: globalized paper assembly

Builds the paper certificate input directly from the GLOBAL qPilot comparison,
without the local PaperXiFSourceLink field
  O.qPilotLogVolume = paperQPilotLogVolume C3.

The global comparison P.average ≤ -O.qPilotLogVolume gives the xi-f ray
membership for qPilotLogVolume := O.qPilotLogVolume and
thetaHullLogVolume := P.signedHullLogVolume.  The qParameter card is an exact
input (global q product log normalization).  The resulting PaperXiFInput feeds
paperCertificate/paperCor312Conclusion, so the final Cor312Conclusion uses the
global object and has NO local=global bridge.

No fake equality; the only exact input is the global qParameter card. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1041GlobalizedAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.S1037GlobalQPilotAuditActual
open LeanFormal.IUT.XiFPaper.S1038GlobalSourceQFinalActual
open LeanFormal.IUT.XiFPaper.S1040GlobalSourceLinkActual
open LeanFormal.IUT.XiFPaper.ThetaLinkFromSource
open MeasureTheory

universe ua uv upi umon ui uL uC uG uX uLabel u uC3 uD3 uM uP

variable {l : PrimeGeFive}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {G' : Type uG} [Group G'] [TopologicalSpace G']
variable {envStrip : FPrimeStrip (FinitePrimePlace 2 7)}
variable {X : Type uX} {label : Type uLabel} [Fintype label] [Nonempty label]
variable (P : PaperSignedHull X label)
variable {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
variable (O : PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
  (Label := Label) (Choice := Choice) (I := I) G' envStrip)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Exact global qParameter card: the global qPilot scalar is -|log qParameter|. -/
structure S1041GlobalQParameterCard where
  qParameter : Real
  qParameter_pos : 0 < qParameter
  qParameter_log_ne_zero : Real.log qParameter ≠ 0
  qPilotLogVolume_eq : O.qPilotLogVolume = -|Real.log qParameter|

/-- Global paper input: qPilotLogVolume is the legacy GLOBAL O.qPilotLogVolume,
theta is P.signedHullLogVolume, ray membership from the global comparison. -/
noncomputable def s1041GlobalPaperXiFInput
    (hcomp : P.procession.average ≤ -O.qPilotLogVolume)
    (D : S1041GlobalQParameterCard (l := l) O) :
    PaperXiFInput P where
  data :=
    { thetaHullLogVolume := P.signedHullLogVolume
      qPilotLogVolume := O.qPilotLogVolume
      qPilot_mem_ray := by
        rw [mem_hullLogVolumeRay_iff, P.signedHullLogVolume_eq_neg_average]
        linarith
      qParameter := D.qParameter
      qParameter_pos := D.qParameter_pos
      qParameter_log_ne_zero := D.qParameter_log_ne_zero
      qPilotLogVolume_eq := D.qPilotLogVolume_eq }
  theta_eq := rfl

/-- Certificate of the global paper input. -/
noncomputable def s1041GlobalCertificate
    (hcomp : P.procession.average ≤ -O.qPilotLogVolume)
    (D : S1041GlobalQParameterCard (l := l) O) :
    StepXIFiniteCertificateSigned label :=
  paperCertificate (I := s1041GlobalPaperXiFInput (P := P) (O := O) hcomp D)

/-- Signed link evidence for the global certificate. -/
noncomputable def s1041GlobalSignedEvidence
    (hcomp : P.procession.average ≤ -O.qPilotLogVolume)
    (D : S1041GlobalQParameterCard (l := l) O)
    (links : FiniteStepXILinkEvidence
      (s1041GlobalCertificate (l := l) P O hcomp D).toStepXIFiniteCertificate) :
    SignedFiniteStepXILinkEvidence
      (s1041GlobalCertificate (l := l) P O hcomp D) :=
  paperSignedLinkEvidence
    (I := s1041GlobalPaperXiFInput (P := P) (O := O) hcomp D) links

/-- Final Cor312Conclusion from the global paper input and finite links. -/
theorem s1041GlobalFinalCor312
    (hcomp : P.procession.average ≤ -O.qPilotLogVolume)
    (D : S1041GlobalQParameterCard (l := l) O)
    (links : FiniteStepXILinkEvidence
      (s1041GlobalCertificate (l := l) P O hcomp D).toStepXIFiniteCertificate) :
    Cor312Conclusion
      ((s1041GlobalCertificate (l := l) P O hcomp D).toContract
        (s1041GlobalSignedEvidence (l := l) P O hcomp D links)) :=
  paperCor312Conclusion
    (I := s1041GlobalPaperXiFInput (P := P) (O := O) hcomp D) links

end LeanFormal.IUT.XiFPaper.S1041GlobalizedAssemblyActual

end
