import tmp.sheaf.xif.paper.S1041GlobalizedAssemblyActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ContractSourceReduction

/-! # S1044: finite link evidence for the S1041 global certificate

The certificate's own hull target supplies the two real comparison bounds
(finiteLinkEvidenceOfHullTarget).  The remaining exact inputs are the
IPL/SHE/APT propositions and their evidence.  We construct the finite link
evidence from exactly those. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1044GlobalFiniteLinksActual

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
open LeanFormal.IUT.XiFPaper.S1041GlobalizedAssemblyActual
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

/-- The exact remaining finite-link fields: IPL/SHE/APT propositions with
their evidence. -/
structure S1044IPLSHEAPTEvidence where
  ipl : Prop
  she : Prop
  apt : Prop
  ipl_evidence : ipl
  she_evidence : she
  apt_evidence : apt

/-- Actual finite link evidence over the S1041 global certificate, from
IPL/SHE/APT evidence; the comparison bounds come from the certificate hull. -/
noncomputable def s1044FiniteLinks
    (hcomp : P.procession.average ≤ -O.qPilotLogVolume)
    (D : S1041GlobalQParameterCard (l := l) O)
    (E : S1044IPLSHEAPTEvidence) :
    FiniteStepXILinkEvidence
      (s1041GlobalCertificate (l := l) P O hcomp D).toStepXIFiniteCertificate :=
  finiteLinkEvidenceOfHullTarget
    (s1041GlobalCertificate (l := l) P O hcomp D).toStepXIFiniteCertificate
    E.ipl E.she E.apt E.ipl_evidence E.she_evidence E.apt_evidence

/-- Final Cor312Conclusion with the actual finite links. -/
theorem s1044GlobalFinalCor312
    (hcomp : P.procession.average ≤ -O.qPilotLogVolume)
    (D : S1041GlobalQParameterCard (l := l) O)
    (E : S1044IPLSHEAPTEvidence) :
    Cor312Conclusion
      ((s1041GlobalCertificate (l := l) P O hcomp D).toContract
        (s1041GlobalSignedEvidence (l := l) P O hcomp D
          (s1044FiniteLinks (l := l) P O hcomp D E))) :=
  s1041GlobalFinalCor312 (l := l) P O hcomp D
    (s1044FiniteLinks (l := l) P O hcomp D E)

/-- Exact minimal finite-link obligation without supplied evidence. -/
def S1044FiniteLinksRequired
    (hcomp : P.procession.average ≤ -O.qPilotLogVolume)
    (D : S1041GlobalQParameterCard (l := l) O) : Prop :=
  Nonempty (FiniteStepXILinkEvidence
    (s1041GlobalCertificate (l := l) P O hcomp D).toStepXIFiniteCertificate)

end LeanFormal.IUT.XiFPaper.S1044GlobalFiniteLinksActual
end
