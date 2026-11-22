import tmp.sheaf.xif.paper.S1051PaperGlobalFinalActual
import tmp.sheaf.xif.paper.S1044GlobalFiniteLinksActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ContractSourceReduction

/-! # S1054: final finite links for the S1051 paper certificate

The paper certificate's hull target supplies the two comparison bounds; the
remaining exact fields are IPL/SHE/APT evidence.  With them the finite links
and the final Cor312Conclusion are actual, conditional only on hullavg and the
paper qParameter card. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1054PaperFinalLinksActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open LeanFormal.IUT.XiFPaper.S1051PaperGlobalFinalActual
open LeanFormal.IUT.XiFPaper.S1044GlobalFiniteLinksActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open MeasureTheory

universe uX uLabel
variable {l : PrimeGeFive}
variable {X : Type uX} {label : Type uLabel} [Fintype label] [Nonempty label]
variable (P : PaperSignedHull X label)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Exact remaining finite-link fields for the S1051 certificate. -/
structure S1054IPLSHEAPTEvidence where
  ipl : Prop
  she : Prop
  apt : Prop
  ipl_evidence : ipl
  she_evidence : she
  apt_evidence : apt

/-- Actual finite links for the S1051 paper certificate. -/
noncomputable def s1054FiniteLinks
    (In : S994FiniteInput T)
    (hullavg :
      P.procession.average =
        -weightedPaperV (l := l) T (s994VS (l := l) T In))
    (D : S1051PaperQParameterCard (l := l) T In)
    (E : S1054IPLSHEAPTEvidence) :
    FiniteStepXILinkEvidence
      (s1051PaperCertificate (l := l) P T In hullavg D).toStepXIFiniteCertificate :=
  finiteLinkEvidenceOfHullTarget
    (s1051PaperCertificate (l := l) P T In hullavg D).toStepXIFiniteCertificate
    E.ipl E.she E.apt E.ipl_evidence E.she_evidence E.apt_evidence

/-- Final Cor312Conclusion with actual finite links; only hullavg and the paper
qParameter card are inputs besides the IPL/SHE/APT evidence. -/
theorem s1054PaperFinalCor312
    (In : S994FiniteInput T)
    (hullavg :
      P.procession.average =
        -weightedPaperV (l := l) T (s994VS (l := l) T In))
    (D : S1051PaperQParameterCard (l := l) T In)
    (E : S1054IPLSHEAPTEvidence) :
    Cor312Conclusion
      ((s1051PaperCertificate (l := l) P T In hullavg D).toContract
        (paperSignedLinkEvidence
          (I := s1051PaperXiFInput (l := l) P T In hullavg D)
          (s1054FiniteLinks (l := l) P T In hullavg D E))) :=
  s1051FinalCor312 (l := l) P T In hullavg D
    (s1054FiniteLinks (l := l) P T In hullavg D E)

/-- Exact minimal finite-link obligation. -/
def S1054FiniteLinksRequired
    (In : S994FiniteInput T)
    (hullavg :
      P.procession.average =
        -weightedPaperV (l := l) T (s994VS (l := l) T In))
    (D : S1051PaperQParameterCard (l := l) T In) : Prop :=
  Nonempty (FiniteStepXILinkEvidence
    (s1051PaperCertificate (l := l) P T In hullavg D).toStepXIFiniteCertificate)

/-- Packaged final paper input with actual finite links. -/
structure S1054PaperFinalInput where
  In : S994FiniteInput T
  hullavg :
    P.procession.average =
      -weightedPaperV (l := l) T (s994VS (l := l) T In)
  card : S1051PaperQParameterCard (l := l) T In
  evidence : S1054IPLSHEAPTEvidence

theorem s1054PaperFinalCor312_of_input
    (H : S1054PaperFinalInput (l := l) P T) :
    Cor312Conclusion
      ((s1051PaperCertificate (l := l) P T H.In H.hullavg H.card).toContract
        (paperSignedLinkEvidence
          (I := s1051PaperXiFInput (l := l) P T H.In H.hullavg H.card)
          (s1054FiniteLinks (l := l) P T H.In H.hullavg H.card H.evidence))) :=
  s1054PaperFinalCor312 (l := l) P T H.In H.hullavg H.card H.evidence

end LeanFormal.IUT.XiFPaper.S1054PaperFinalLinksActual
end
