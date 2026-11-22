import tmp.sheaf.xif.paper.S1680QPilotObjectActual
import tmp.sheaf.xif.paper.S1554SignedHullFromQActual

/-! # S1684: OrigXiFThetaLinkActual from the actual S1680-style O and S1554

S1680 constructs the full PaperQPilotObject on the S1487 faithful input,
while S1554 proves the two ThetaLink fields for every O over the S1527
assembled input and every actual signed hull D.  The two inputs are not the
same OriginalInput, so the S1680 object cannot be used verbatim.  This file
builds the same-shape actual object O on the S1527 input (same actual S1679
O(-D) line bundle, concreteInput boundary, sourceQPilotStrip, oneColumn,
selfKummerArrow, sourceQPilotSignedLog) and applies S1554 to obtain the actual
OrigXiFThetaLinkActual O D (S1527C3 ...).

EXACT ALIGNMENT FIELD if one insists on the original S1680 object:
  S1680Input = S1527Input l R ...
is not available; S1680Input uses S1487FaithfulSourceData, S1527Input uses the
S1280SourceData assembled from R.  This file does not fake that equality.

No native donor D, no R -> ThetaLink wrapper, no Nonempty gate is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1684ThetaLinkFromActualOActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1477OScalarBridgeActual
open LeanFormal.IUT.XiFPaper.S1527OOrderEqualityActual
open LeanFormal.IUT.XiFPaper.S1554SignedHullFromQActual
open LeanFormal.IUT.XiFPaper.S1679CompleteODCarrierActual
open LeanFormal.IUT.XiFPaper.OrigXiF
open LeanFormal.IUT.XiFPaper.OrigXiF.OrigXiFPaperQPilotObjectActual
open LeanFormal.IUT.XiFPaper.OrigXiFPaperQPilotScalarActual
open LeanFormal.IUT.XiFPaper.OrigXiFThetaLinkActual
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual

universe u uG uL uC uX

variable {l : PrimeGeFive}

/-- The same-shape actual q-pilot object on the S1527 assembled input. -/
noncomputable def s1684QPilotObject
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      (S1527Input l R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat)
      (OrigXiFPaperSourceKummerGroup l) (OrigXiFPaperSourceStrip l) where
  boundary := OrigXiFPaperSourceBoundary l
  strip := OrigXiFPaperSourceStrip l
  strip_eq_source := rfl
  oneColumn := actualOneColumnFinitePrimePlace
  lineBundle := s1679Carrier l
  logKummer := OrigXiFPaperSourceKummerArrow l
  qPilotLogVolume :=
    sourceQPilotSignedLog (S1527Input l R redCompat hredCompat torCompat
      htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat
      hcusCompat).initial
  qPilotLogVolume_eq := rfl
  paper_strip_identification :=
    OrigXiFPaperStripIdentified (OrigXiFPaperSourceBoundary l)
      (OrigXiFPaperSourceStrip l)
  paper_lineBundle_identification :=
    S1679PaperLineBundleIdentified l
  paper_logKummer_identification :=
    OrigXiFPaperLogKummerIdentified (OrigXiFPaperSourceKummerArrow l)
  paper_qPilot_log_identification :=
    OrigXiFPaperQPilotScalarIdentified (S1527Input l R redCompat hredCompat
      torCompat htorCompat orbCompat horbCompat secCompat hsecCompat
      cusCompat hcusCompat).initial
      (sourceQPilotSignedLog (S1527Input l R redCompat hredCompat torCompat
        htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat
        hcusCompat).initial)

/-- The actual ThetaLink for the same-shape object and every actual signed
hull datum D, using S1554. -/
theorem s1684OrigXiFThetaLinkActual
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {X : Type uX} [TopologicalSpace X]
    (D : OrigXiFPaperSignedHullData X l) :
    OrigXiFThetaLinkActual
      (s1684QPilotObject R redCompat hredCompat torCompat htorCompat
        orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)
      D
      (S1527C3 l R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat) :=
  S1554_origXiFThetaLinkActual l R redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat
    (s1684QPilotObject R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat) D

end LeanFormal.IUT.XiFPaper.S1684ThetaLinkFromActualOActual

end
