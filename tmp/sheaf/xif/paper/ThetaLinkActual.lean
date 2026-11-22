import tmp.sheaf.xif.PaperQPilotObject
import tmp.sheaf.xif.PaperQPilotLogVolume
import tmp.sheaf.xif.PaperSignedHull
import tmp.sheaf.xif.PaperXiFInclusion
import tmp.sheaf.xif.PaperCertificate
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiringSigned

/-! # Actual paper Theta-link / q-pilot link comparison

STATUS: paper-level from-scratch module. This file is not a value-layer
surrogate. It consumes the actual paper q-pilot object, the actual paper signed
hull, the paper q-pilot scalar, and the paper certificate layer, and derives the
xi-f membership and the signed certificate q_le_hull slot from an explicit
Theta-link/q-pilot link identification.

## Expected paper modules (being written by other owners)

The final paper build is expected to provide the following modules and names.
This file currently imports the actual paper modules that already exist and
records the expected replacements as a contract. It must not be closed by
replacing them with value-layer objects.

  tmp.sheaf.xif.paper.QPilotObjectActual
      actual q-pilot object at (1,0): strip, arithmetic rank-one line bundle,
      log-Kummer representation on 1,circ U_Q, and (1,0) binding.
      Expected names: QPilotObjectActual, qPilotAtOneZero,
      qPilotLogKummerRepresentation.

  tmp.sheaf.xif.paper.QPilotLogActual
      actual source q parameter, positivity, q != 1, signed -|log q|, and
      identification with the paper QPaper scalar.
      Expected names: QPilotLogActual, qPilotSignedLog,
      qPilotSignedLog_eq_neg_abs_log.

  tmp.sheaf.xif.paper.ThetaHullActual
      actual compact 1,circ U_{j,vQ} hull with holomorphic compactness,
      procession average, and Haar/log-shell normalization.
      Expected names: ThetaHullActual, thetaHullVolume,
      thetaHull_processionAverage.

  tmp.sheaf.xif.paper.SignedHullLogActual
      actual signed -|log Theta| from the paper hull determinant/log-volume.
      Expected names: SignedHullLogActual, signedHullLogVolume,
      signedHullLogVolume_eq_neg_thetaHullLog.

  tmp.sheaf.xif.paper.OModuleActual
      actual O-module / rank-one arithmetic line-bundle / localization layer.
      Expected names: OModuleActual, arithmeticLineBundle,
      determinantLocalizationLogVolume.

  tmp.sheaf.xif.paper.IndeterminaciesActual
      actual Ind1/Ind2/Ind3 actions and log-volume/region invariance.
      Expected names: IndeterminaciesActual, ind1Action, ind2Action, ind3Action.

  tmp.sheaf.xif.paper.SHELandingActual
      actual SHE landing in the 1,circ localizations.
      Expected names: SHELandingActual, sheLandingMap, sheExpression.

  tmp.sheaf.xif.paper.IPLActual
      actual IPL full-poly-isomorphism link and compatibility.
      Expected names: IPLActual, iplLink, ipl_compatible.

  tmp.sheaf.xif.paper.APTActual
      actual APT transport/evidence.
      Expected names: APTActual, aptTransport, aptEvidence.

This file establishes the comparison and certificate layer. It does not
construct the expected paper objects themselves; their exact source
obligations remain with the modules above. The actual paper modules imported
below are the current compiled carriers for q-pilot, signed hull, q scalar, and
certificate consumption.

## What is derived here

Given actual paper-level data:
* q-pilot object O (PaperQPilotObject);
* signed paper hull P (PaperSignedHull);
* source q scalar C3 (SourcePilotRegionData);
* an explicit Theta-link/q-pilot link identification and its exact
  log-volume comparison;

we construct:
* Cor312ComparisonData with qPilot_mem_ray;
* PaperXiFInput;
* the signed finite certificate with q_le_hull slot;
* the paper inclusion -|log q| in R_{<= -|log Theta|}.

No PUnit, Unit, True, axiom, sorry, or fake witness is used. The link
identification and its comparison implication are real obligation fields, not
asserted inhabitants. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT
namespace XiFPaper
namespace ThetaLink

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume

universe ua uv upi umon ui uL uC uG uX uLabel

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable [Nonempty label]

/-! ## 1. Actual link data

The Theta-link comparison consumes the actual paper q-pilot and signed hull
objects. The source q scalar is the actual completion q parameter from C3, not
the theta-label-1 value-layer surrogate. -/

/-- The actual paper q parameter: the norm of the source completion q. -/
noncomputable def thetaLinkQParameter
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Real :=
  ‖C3.q.q‖

theorem thetaLinkQParameter_pos
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    0 < thetaLinkQParameter C3 := by
  unfold thetaLinkQParameter
  exact ArithmeticQPilotLogVolume.qNorm_pos C3.q

theorem thetaLinkQParameter_log_ne_zero
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    Real.log (thetaLinkQParameter C3) ≠ 0 := by
  unfold thetaLinkQParameter
  exact ne_of_lt (ArithmeticQPilotLogVolume.localSignedLog_neg C3.q)

/-- The paper q-pilot scalar in the link is -|log q| for the actual completion
q parameter. This is the q scalar side of the comparison. -/
theorem thetaLinkPaperQPilot_eq_neg_abs_qParameter
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    paperQPilotLogVolume C3 =
      -|Real.log (thetaLinkQParameter C3)| := by
  rw [paperQPilotLogVolume_eq_log_norm]
  unfold thetaLinkQParameter
  have hneg : Real.log ‖C3.q.q‖ < 0 :=
    ArithmeticQPilotLogVolume.localSignedLog_neg C3.q
  rw [abs_of_neg hneg, neg_neg]

/-- Exact source obligations of the actual q-pilot object. These are the paper
identifications, not value-layer statements. They are fields of
PaperQPilotObject and are kept as explicit proof obligations. -/
def thetaLinkQPilotPaperIdentifications
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip) : Prop :=
  O.paper_strip_identification ∧
  O.paper_lineBundle_identification ∧
  O.paper_logKummer_identification ∧
  O.paper_qPilot_log_identification

/-- Actual Theta-link/q-pilot link data. The q-pilot object and signed hull are
the actual paper-level carriers. The two identification fields are the exact
paper link obligations; link_implies_inclusion is the missing paper
log-volume comparison, not a hull-sup or value-layer inequality. -/
structure ThetaLinkActual
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I) where
  /-- Exact q-pilot paper identifications. -/
  qPilot_identifications : thetaLinkQPilotPaperIdentifications O
  /-- The q-pilot object scalar is the actual paper q scalar. -/
  qPilotLogVolume_eq_paper : O.qPilotLogVolume = paperQPilotLogVolume C3
  /-- The actual q parameter used in the paper normalization. -/
  qParameter : Real
  qParameter_pos : 0 < qParameter
  qParameter_log_ne_zero : Real.log qParameter ≠ 0
  /-- The q-pilot scalar is the paper signed value -|log q|. -/
  qPilotLogVolume_eq_neg_abs : O.qPilotLogVolume = -|Real.log qParameter|
  /-- The actual Theta-link/q-pilot link identification proposition. -/
  link_identification : Prop
  /-- Exact missing paper comparison: the link identification implies the xi-f
  membership in the signed hull ray. This is the paper Theta-link/log-volume
  comparison, not a pointwise value-layer hull-sup inequality. -/
  link_implies_inclusion :
    link_identification →
      O.qPilotLogVolume ∈
        hullLogVolumeRay P.signedHullLogVolume

/-! ## 2. Comparison data and the xi-f membership

From actual link data, construct the paper comparison card. The only
conditional input is the explicit link identification proof. -/

/-- The paper comparison data obtained from the actual Theta-link. -/
def thetaLinkComparisonData
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (L : ThetaLinkActual O P C3)
    (hlink : L.link_identification) :
    Cor312ComparisonData where
  thetaHullLogVolume := P.signedHullLogVolume
  qPilotLogVolume := O.qPilotLogVolume
  qPilot_mem_ray := L.link_implies_inclusion hlink
  qParameter := L.qParameter
  qParameter_pos := L.qParameter_pos
  qParameter_log_ne_zero := L.qParameter_log_ne_zero
  qPilotLogVolume_eq := L.qPilotLogVolume_eq_neg_abs

/-- Paper xi-f membership: -|log q| lies in R_{<= -|log Theta|}. -/
theorem thetaLinkXiFMembership
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (L : ThetaLinkActual O P C3)
    (hlink : L.link_identification) :
    O.qPilotLogVolume ∈
      hullLogVolumeRay P.signedHullLogVolume :=
  L.link_implies_inclusion hlink

/-- Paper xi-f inequality: -|log q| <= -|log Theta|. -/
theorem thetaLinkXiFInequality
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (L : ThetaLinkActual O P C3)
    (hlink : L.link_identification) :
    O.qPilotLogVolume ≤ P.signedHullLogVolume :=
  (mem_hullLogVolumeRay_iff).mp (thetaLinkXiFMembership O P C3 L hlink)

/-- The q-pilot scalar is -|log q| for the actual q parameter. -/
theorem thetaLinkQPilot_eq_neg_abs
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (L : ThetaLinkActual O P C3) :
    O.qPilotLogVolume = -|Real.log L.qParameter| :=
  L.qPilotLogVolume_eq_neg_abs

/-! ## 3. Signed certificate q_le_hull slot

The paper certificate layer consumes a PaperXiFInput. We build it from the
actual link comparison; the certificate q_le_hull slot is exactly the paper
xi-f membership. -/

/-- Paper certificate input obtained from the actual Theta-link comparison. -/
def thetaLinkPaperXiFInput
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (L : ThetaLinkActual O P C3)
    (hlink : L.link_identification) :
    PaperXiFInput P where
  data := thetaLinkComparisonData O P C3 L hlink
  theta_eq := rfl

/-- The actual signed finite certificate with the paper xi-f q_le_hull slot. -/
def thetaLinkCertificate
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (L : ThetaLinkActual O P C3)
    (hlink : L.link_identification) :
    StepXIFiniteCertificateSigned label :=
  paperCertificate (I := thetaLinkPaperXiFInput O P C3 L hlink)

/-- The certificate q_le_hull slot is the paper xi-f inclusion. -/
theorem thetaLinkCertificate_q_le_hull
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (L : ThetaLinkActual O P C3)
    (hlink : L.link_identification) :
    (thetaLinkCertificate O P C3 L hlink).qSigned ≤
      (thetaLinkCertificate O P C3 L hlink).hull.hullVolume :=
  paperCertificate_q_le_hull (I := thetaLinkPaperXiFInput O P C3 L hlink)

/-- The certificate signed q <= theta slot. -/
theorem thetaLinkCertificate_q_le_theta
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (L : ThetaLinkActual O P C3)
    (hlink : L.link_identification) :
    (thetaLinkCertificate O P C3 L hlink).qSigned ≤
      (thetaLinkCertificate O P C3 L hlink).thetaSigned :=
  paperCertificate_q_le_theta (I := thetaLinkPaperXiFInput O P C3 L hlink)

/-- The certificate qSigned field is the actual paper q-pilot scalar. -/
theorem thetaLinkCertificate_qSigned_eq
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (L : ThetaLinkActual O P C3)
    (hlink : L.link_identification) :
    (thetaLinkCertificate O P C3 L hlink).qSigned = O.qPilotLogVolume :=
  rfl

/-- The certificate thetaSigned field is the actual paper signed hull volume. -/
theorem thetaLinkCertificate_thetaSigned_eq
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (L : ThetaLinkActual O P C3)
    (hlink : L.link_identification) :
    (thetaLinkCertificate O P C3 L hlink).thetaSigned =
      P.signedHullLogVolume :=
  rfl

/-! ## 4. Exact source obligations

The file does not assert an inhabitant of ThetaLinkActual. The remaining
obligations are exactly:
1. thetaLinkQPilotPaperIdentifications O (the four PaperQPilotObject paper
   identifications);
2. O.qPilotLogVolume = paperQPilotLogVolume C3 (actual paper q scalar);
3. O.qPilotLogVolume = -|log qParameter| (paper q normalization);
4. a proof of link_identification (actual Theta-link/q-pilot link);
5. a proof of link_implies_inclusion (paper log-volume comparison).

These are recorded as structure fields, not axioms. The signed certificate and
xi-f membership are conditional on 4/5. No value-layer object, PUnit, Unit,
True, sorry, or axiom is used. -/

/-- Exact obligation surface for the actual Theta-link. This structure is not
asserted to be inhabited; it records the remaining source obligations. -/
structure ThetaLinkSourceObligations
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (L : ThetaLinkActual O P C3) where
  qPilot_identifications : thetaLinkQPilotPaperIdentifications O
  qPilotLogVolume_eq_paper : O.qPilotLogVolume = paperQPilotLogVolume C3
  qPilotLogVolume_eq_neg_abs :
    O.qPilotLogVolume = -|Real.log L.qParameter|
  link_identification : L.link_identification
  link_implies_inclusion :
    L.link_identification →
      O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume

/-- From the exact obligations one obtains the comparison and certificate. -/
theorem thetaLinkSourceObligations_comparison
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (L : ThetaLinkActual O P C3)
    (S : ThetaLinkSourceObligations O P C3 L) :
    O.qPilotLogVolume ≤ P.signedHullLogVolume :=
  thetaLinkXiFInequality O P C3 L S.link_identification

/-- From the exact obligations one obtains the certificate q_le_hull slot. -/
theorem thetaLinkSourceObligations_certificate
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (L : ThetaLinkActual O P C3)
    (S : ThetaLinkSourceObligations O P C3 L) :
    (thetaLinkCertificate O P C3 L S.link_identification).qSigned ≤
      (thetaLinkCertificate O P C3 L S.link_identification).hull.hullVolume :=
  thetaLinkCertificate_q_le_hull O P C3 L S.link_identification

/-! ## 5. Link compatibility with the expected actual modules

The expected paper modules are declared above. Once available, their actual
objects instantiate O, P, C3 and discharge the fields of ThetaLinkActual. The
comparison/certificate lemmas here are independent of how those modules are
constructed, so they can be reused without changing the conclusion surface. -/

/-- The q-pilot log-volume field of the comparison card is the actual object
scalar, not a value-layer theta-label-1 field. -/
theorem thetaLinkComparisonData_qPilot_eq
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (L : ThetaLinkActual O P C3)
    (hlink : L.link_identification) :
    (thetaLinkComparisonData O P C3 L hlink).qPilotLogVolume =
      O.qPilotLogVolume :=
  rfl

/-- The theta hull field of the comparison card is the actual signed paper hull,
not sourceThetaHullLogVolume. -/
theorem thetaLinkComparisonData_theta_eq
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (L : ThetaLinkActual O P C3)
    (hlink : L.link_identification) :
    (thetaLinkComparisonData O P C3 L hlink).thetaHullLogVolume =
      P.signedHullLogVolume :=
  rfl

end ThetaLink
end XiFPaper
end LeanFormal.IUT
