import tmp.sheaf.xif.paper.S1042GlobalQParameterCardActual
import tmp.sheaf.xif.paper.S1044GlobalFiniteLinksActual
import tmp.sheaf.xif.paper.S1043CorrectedBridgeExactActual
import tmp.sheaf.xif.paper.S1040GlobalSourceLinkActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual

-- S1045: final assembly using S1042 actual global qParameter card,
-- S1044 actual finite links, and the S1043 corrected bridge.
-- Exact inputs: nonempty bad places, S994FiniteInput, corrected bridge,
-- global paper q field O.qPilotLogVolume=globalQPilotLog, IPL/SHE/APT evidence.
-- No local=global bridge.

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1045GlobalFinalAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S1041GlobalizedAssemblyActual
open LeanFormal.IUT.XiFPaper.S1042GlobalQParameterCardActual
open LeanFormal.IUT.XiFPaper.S1044GlobalFiniteLinksActual
open LeanFormal.IUT.XiFPaper.S1043CorrectedBridgeExactActual
open LeanFormal.IUT.XiFPaper.S1040GlobalSourceLinkActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1037GlobalQPilotAuditActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open MeasureTheory

universe ua uv upi umon ui uL uC uG uX uLabel u

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

/-- Exact inputs that remain after S1042/S1044/S1043 are used. -/
structure S1045ExactFinalInput where
  hbad : Nonempty I.initial.badPlaces
  In : S994FiniteInput T
  bridge : S1037CorrectedBridge (l := l) P T In
  globalQ : S1040GlobalPaperQField (l := l) O T
  ev : S1044IPLSHEAPTEvidence

/-- Assemble the exact input using S1043's corrected-bridge exact data. -/
noncomputable def s1045ExactFinalInputOfS1043
    (hbad : Nonempty I.initial.badPlaces)
    (In : S994FiniteInput T)
    (hexact : S1043CorrectedBridgeExact (l := l) P T In)
    (hglobal : S1040GlobalPaperQField (l := l) O T)
    (E : S1044IPLSHEAPTEvidence) :
    S1045ExactFinalInput (l := l) P O T where
  hbad := hbad
  In := In
  bridge := s1043BridgeOfExact (l := l) P T In hexact
  globalQ := hglobal
  ev := E

noncomputable def s1045Card
    (H : S1045ExactFinalInput (l := l) P O T) :
    S1041GlobalQParameterCard (l := l) O :=
  s1042GlobalQParameterCard (l := l) O H.hbad

theorem s1045Hcomp
    (H : S1045ExactFinalInput (l := l) P O T) :
    P.procession.average ≤ -O.qPilotLogVolume :=
  s1040GlobalLinkIdentification_of_bridge (l := l) P O T
    H.In H.bridge H.globalQ

noncomputable def s1045Links
    (H : S1045ExactFinalInput (l := l) P O T) :
    FiniteStepXILinkEvidence
      (s1041GlobalCertificate (l := l) P O
        (s1045Hcomp (l := l) P O T H) (s1045Card (l := l) P O T H)).toStepXIFiniteCertificate :=
  s1044FiniteLinks (l := l) P O
    (s1045Hcomp (l := l) P O T H) (s1045Card (l := l) P O T H) H.ev

/-- Final Cor312Conclusion actual from S1042 card + S1044 links + S1043 bridge. -/
theorem s1045GlobalFinalCor312
    (H : S1045ExactFinalInput (l := l) P O T) :
    Cor312Conclusion
      ((s1041GlobalCertificate (l := l) P O
          (s1045Hcomp (l := l) P O T H)
          (s1045Card (l := l) P O T H)).toContract
        (s1041GlobalSignedEvidence (l := l) P O
          (s1045Hcomp (l := l) P O T H)
          (s1045Card (l := l) P O T H)
          (s1045Links (l := l) P O T H))) :=
  s1044GlobalFinalCor312 (l := l) P O
    (s1045Hcomp (l := l) P O T H)
    (s1045Card (l := l) P O T H) H.ev

def S1045FinalAssemblyRequired : Prop :=
  Nonempty (S1045ExactFinalInput (l := l) P O T)

#check s1045GlobalFinalCor312
#check S1045ExactFinalInput
#check S1045FinalAssemblyRequired

end LeanFormal.IUT.XiFPaper.S1045GlobalFinalAssemblyActual

end