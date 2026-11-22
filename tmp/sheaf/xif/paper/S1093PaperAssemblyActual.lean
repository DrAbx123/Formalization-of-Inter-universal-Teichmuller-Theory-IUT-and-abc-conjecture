import tmp.sheaf.xif.paper.S1070CanonicalQPilotRegionActual
import tmp.sheaf.xif.paper.S1073RootStackPaperThetaHullActual
import tmp.sheaf.xif.PaperCertificate
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ContractSourceReduction

/-! # S1093: paper-level assembly canonical q[1u] vs root-stack Theta hull

Uses canonicalQPilotLog (q[1u]) and rootStackPaperThetaHullLog (root-stack Theta
hull), not S1051/qPilotPaperRegion.  The PaperXiFInput/certificate are built
from an exact per-b inequality, the paper signed-hull identification, and a
qParameter card.  Finite links use the certificate hull target. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1093PaperAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1070CanonicalQPilotRegionActual
open LeanFormal.IUT.XiFPaper.S1073RootStackPaperThetaHullActual
open MeasureTheory

universe uX uLabel u
variable {l : PrimeGeFive}
variable {X : Type uX} {label : Type uLabel} [Fintype label] [Nonempty label]
variable (P : PaperSignedHull X label)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Exact paper data for the canonical q[1u] / root-stack Theta assembly. -/
structure S1093PaperComparisonData where
  qParameter : Real
  qParameter_pos : 0 < qParameter
  qParameter_log_ne_zero : Real.log qParameter ≠ 0
  qPilot_eq_qParameter :
    canonicalQPilotLog (l := l) T b = -|Real.log qParameter|
  perBInequality :
    canonicalQPilotLog (l := l) T b ≤
      rootStackPaperThetaHullLog (l := l) T b
  theta_agrees :
    rootStackPaperThetaHullLog (l := l) T b = P.signedHullLogVolume

/-- Paper comparison data from the exact inputs. -/
noncomputable def s1093ComparisonData
    (H : S1093PaperComparisonData (l := l) P T b) :
    Cor312ComparisonData where
  thetaHullLogVolume := rootStackPaperThetaHullLog (l := l) T b
  qPilotLogVolume := canonicalQPilotLog (l := l) T b
  qPilot_mem_ray := by
    rw [mem_hullLogVolumeRay_iff]
    exact H.perBInequality
  qParameter := H.qParameter
  qParameter_pos := H.qParameter_pos
  qParameter_log_ne_zero := H.qParameter_log_ne_zero
  qPilotLogVolume_eq := H.qPilot_eq_qParameter

/-- Paper Xi-F input. -/
noncomputable def s1093PaperXiFInput
    (H : S1093PaperComparisonData (l := l) P T b) :
    PaperXiFInput P where
  data := s1093ComparisonData (l := l) P T b H
  theta_eq := H.theta_agrees

/-- Paper certificate. -/
noncomputable def s1093Certificate
    (H : S1093PaperComparisonData (l := l) P T b) :
    StepXIFiniteCertificateSigned label :=
  paperCertificate (I := s1093PaperXiFInput (l := l) P T b H)

/-- Exact remaining finite-link fields. -/
structure S1093IPLSHEAPTEvidence where
  ipl : Prop
  she : Prop
  apt : Prop
  ipl_evidence : ipl
  she_evidence : she
  apt_evidence : apt

/-- Actual finite links over the paper certificate hull. -/
noncomputable def s1093FiniteLinks
    (H : S1093PaperComparisonData (l := l) P T b)
    (E : S1093IPLSHEAPTEvidence) :
    FiniteStepXILinkEvidence
      (s1093Certificate (l := l) P T b H).toStepXIFiniteCertificate :=
  finiteLinkEvidenceOfHullTarget
    (s1093Certificate (l := l) P T b H).toStepXIFiniteCertificate
    E.ipl E.she E.apt E.ipl_evidence E.she_evidence E.apt_evidence

/-- Final Cor312Conclusion from the paper assembly and finite links. -/
theorem s1093FinalCor312
    (H : S1093PaperComparisonData (l := l) P T b)
    (E : S1093IPLSHEAPTEvidence) :
    Cor312Conclusion
      ((s1093Certificate (l := l) P T b H).toContract
        (paperSignedLinkEvidence
          (I := s1093PaperXiFInput (l := l) P T b H)
          (s1093FiniteLinks (l := l) P T b H E))) :=
  paperCor312Conclusion
    (I := s1093PaperXiFInput (l := l) P T b H)
    (s1093FiniteLinks (l := l) P T b H E)

/-- Exact remaining assembly inputs. -/
def S1093ExactMinimum (H : S1093PaperComparisonData (l := l) P T b) : Prop :=
  Nonempty (FiniteStepXILinkEvidence
    (s1093Certificate (l := l) P T b H).toStepXIFiniteCertificate)

end LeanFormal.IUT.XiFPaper.S1093PaperAssemblyActual
end
