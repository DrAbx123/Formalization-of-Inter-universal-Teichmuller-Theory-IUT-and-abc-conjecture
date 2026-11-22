import tmp.sheaf.xif.paper.ThetaLinkActual
import tmp.sheaf.xif.paper.PaperXiFSpec
import tmp.sheaf.xif.paper.PaperXiFTheorem
import tmp.sheaf.xif.PaperXiFInclusion
import tmp.sheaf.xif.PaperCertificate
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiringSigned

/-! # Paper-level conditional xi-f proof

STATUS: paper-level proof composition. No value-layer surrogate, no PUnit/Unit,
no True, no axiom, no sorry, no asserted inhabitant.

This file composes:
* ThetaLinkActual: actual q-pilot object + signed hull + paper q scalar + explicit
  Theta-link/q-pilot link identification and its exact comparison obligation;
* PaperXiFInclusion: the paper-level inclusion data derived from that link;
* PaperXiFSpec: the scalar statement -|log q| in R_{<= -|log Theta|} and its
  real-arithmetic cTheta bound;
* PaperCertificate: the signed finite certificate with its q_le_hull slot.

It proves, conditionally on the exact link identification:
1. paperXiF (paperQParameter C3) P.signedHullLogVolume;
2. the signed certificate q_le_hull and q_le_theta slots;
3. -1 <= cTheta for every cTheta satisfying the paper theta bound.

No inhabitant of ThetaLinkActual or PaperXiFInclusion is constructed. The exact
remaining obligations are listed in PaperXiFThetaLinkObligations below. This is
the paper-level conditional proof layer, not a target-accepted closure. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT
namespace XiFPaper
namespace Proof

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.ThetaLink

universe ua uv upi umon ui uL uC uG uX uLabel

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label] [Nonempty label]

variable {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
variable {P : PaperSignedHull X label}
variable {C3 : SourcePilotRegionData (l := l) (V := V) I}

/-! ## 1. From the actual Theta-link to the paper inclusion surface -/

/-- Convert the actual Theta-link/q-pilot data to the paper inclusion surface.
The source identifications and exact link fields are carried over unchanged;
nothing is weakened to a value-layer inequality. -/
def thetaLinkToPaperSourceLink
    (L : ThetaLinkActual O P C3) : PaperXiFSourceLink O P C3 where
  source_identifications := by
    simpa [thetaLinkQPilotPaperIdentifications] using L.qPilot_identifications
  qPilotLogVolume_eq_paper := L.qPilotLogVolume_eq_paper
  link_identification := L.link_identification
  link_implies_inclusion := L.link_implies_inclusion

/-- The paper-level xi-f inclusion obtained from the actual Theta-link and an
explicit proof of its link identification. -/
def thetaLinkToPaperInclusion
    (L : ThetaLinkActual O P C3) (hlink : L.link_identification) :
    PaperXiFInclusion O P C3 where
  link := thetaLinkToPaperSourceLink L
  link_holds := hlink

/-- The paper scalar xi-f statement from the actual Theta-link. -/
theorem paperXiF_of_thetaLink
    (L : ThetaLinkActual O P C3) (hlink : L.link_identification) :
    paperXiF (paperQParameter C3) P.signedHullLogVolume :=
  LeanFormal.IUT.XiFPaper.paperXiF_of_inclusion
    (thetaLinkToPaperInclusion L hlink)

/-- The signed q-pilot log-volume from the link is the paper -|log q|. -/
theorem paperXiF_qPilot_eq_of_thetaLink
    (L : ThetaLinkActual O P C3) (hlink : L.link_identification) :
    O.qPilotLogVolume = paperSignedLog (paperQParameter C3) :=
  LeanFormal.IUT.XiFPaper.paperXiF_qPilot_eq_paperSignedLog
    (thetaLinkToPaperInclusion L hlink)

/-- The scalar data package for the actual Theta-link. -/
def paperXiFScalarDataOfThetaLink
    (L : ThetaLinkActual O P C3) (hlink : L.link_identification) :
    PaperXiFScalarData :=
  LeanFormal.IUT.XiFPaper.paperXiFScalarDataOfInclusion
    (thetaLinkToPaperInclusion L hlink)

/-! ## 2. Signed certificate from the actual link

The certificate is the actual signed finite certificate of PaperCertificate,
constructed from the paper comparison data of the Theta-link. The q_le_hull slot
is the paper xi-f inclusion, not a value-layer hull-sup inequality. -/

/-- The signed finite certificate associated to the actual Theta-link. -/
def thetaLinkCertificateOfProof
    (L : ThetaLinkActual O P C3) (hlink : L.link_identification) :
    StepXIFiniteCertificateSigned label :=
  thetaLinkCertificate O P C3 L hlink

/-- The certificate q_le_hull slot is the paper xi-f inclusion. -/
theorem thetaLinkCertificate_q_le_hull_of_proof
    (L : ThetaLinkActual O P C3) (hlink : L.link_identification) :
    (thetaLinkCertificateOfProof L hlink).qSigned ≤
      (thetaLinkCertificateOfProof L hlink).hull.hullVolume :=
  thetaLinkCertificate_q_le_hull O P C3 L hlink

/-- The certificate q_le_theta slot. -/
theorem thetaLinkCertificate_q_le_theta_of_proof
    (L : ThetaLinkActual O P C3) (hlink : L.link_identification) :
    (thetaLinkCertificateOfProof L hlink).qSigned ≤
      (thetaLinkCertificateOfProof L hlink).thetaSigned :=
  thetaLinkCertificate_q_le_theta O P C3 L hlink

/-- The certificate qSigned scalar is the actual q-pilot object scalar. -/
theorem thetaLinkCertificate_qSigned_eq_of_proof
    (L : ThetaLinkActual O P C3) (hlink : L.link_identification) :
    (thetaLinkCertificateOfProof L hlink).qSigned = O.qPilotLogVolume :=
  rfl

/-- The certificate thetaSigned scalar is the actual signed paper hull volume. -/
theorem thetaLinkCertificate_thetaSigned_eq_of_proof
    (L : ThetaLinkActual O P C3) (hlink : L.link_identification) :
    (thetaLinkCertificateOfProof L hlink).thetaSigned =
      P.signedHullLogVolume :=
  rfl

/-! ## 3. The composed paper-level xi-f result -/

/-- The three paper-level outputs: scalar xi-f, signed certificate q_le_hull,
and the cTheta lower bound. The cTheta bound is quantified over every paper
theta comparison input; it is not a fixed numeric assertion. -/
structure PaperXiFResult
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I) where
  qParameter : Real
  thetaHullLogVolume : Real
  qParameter_pos : 0 < qParameter
  qParameter_log_ne_zero : Real.log qParameter ≠ 0
  xi_f : paperXiF qParameter thetaHullLogVolume
  certificate : StepXIFiniteCertificateSigned label
  certificate_q_le_hull : certificate.qSigned ≤ certificate.hull.hullVolume
  certificate_q_le_theta : certificate.qSigned ≤ certificate.thetaSigned
  cTheta_lowerBound :
    ∀ cTheta : Real,
      thetaHullLogVolume ≤ cTheta * |Real.log qParameter| → -1 ≤ cTheta

/-- Compose the actual Theta-link data into the paper-level xi-f result.
Conditional on the explicit link identification only; no inhabitant is
asserted. -/
def paperXiFResultOfThetaLink
    (L : ThetaLinkActual O P C3) (hlink : L.link_identification) :
    PaperXiFResult O P C3 where
  qParameter := paperQParameter C3
  thetaHullLogVolume := P.signedHullLogVolume
  qParameter_pos := paperQParameter_pos C3
  qParameter_log_ne_zero := paperQParameter_log_ne_zero C3
  xi_f := paperXiF_of_thetaLink L hlink
  certificate := thetaLinkCertificateOfProof L hlink
  certificate_q_le_hull := thetaLinkCertificate_q_le_hull_of_proof L hlink
  certificate_q_le_theta := thetaLinkCertificate_q_le_theta_of_proof L hlink
  cTheta_lowerBound := by
    intro cTheta hc
    exact LeanFormal.IUT.XiFPaper.paperXiF_cTheta_lowerBound
      (thetaLinkToPaperInclusion L hlink) hc

/-- The scalar xi-f statement extracted from the result. -/
theorem paperXiFResult_xi_f
    (R : PaperXiFResult O P C3) :
    paperXiF R.qParameter R.thetaHullLogVolume :=
  R.xi_f

/-- The certificate q_le_hull slot extracted from the result. -/
theorem paperXiFResult_q_le_hull
    (R : PaperXiFResult O P C3) :
    R.certificate.qSigned ≤ R.certificate.hull.hullVolume :=
  R.certificate_q_le_hull

/-- The cTheta lower bound extracted from the result. -/
theorem paperXiFResult_cTheta_lowerBound
    (R : PaperXiFResult O P C3) {cTheta : Real}
    (hc : R.thetaHullLogVolume ≤ cTheta * |Real.log R.qParameter|) :
    -1 ≤ cTheta :=
  R.cTheta_lowerBound cTheta hc

/-! ## 4. Exact obligation surface

The actual Theta-link and its link identification are the only inputs not
constructed by this file. The structure below records the exact obligations.
It is not asserted to be inhabited. -/

/-- Exact paper-level obligations for the composed xi-f proof. -/
structure PaperXiFThetaLinkObligations
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

/-- The composed paper xi-f proof from the exact obligations. This is the
paper-level conditional theorem; the link identification itself is an
obligation, not a constructed source theorem here. -/
def paperXiFResult_of_obligations
    (L : ThetaLinkActual O P C3)
    (S : PaperXiFThetaLinkObligations O P C3 L) :
    PaperXiFResult O P C3 :=
  paperXiFResultOfThetaLink L S.link_identification

/-- Paper scalar xi-f from the exact obligations. -/
theorem paperXiF_of_obligations
    (L : ThetaLinkActual O P C3)
    (S : PaperXiFThetaLinkObligations O P C3 L) :
    paperXiF (paperQParameter C3) P.signedHullLogVolume :=
  by
    simpa [paperXiFResult_of_obligations, paperXiFResultOfThetaLink] using
      (paperXiFResult_of_obligations L S).xi_f

/-- Signed certificate q_le_hull from the exact obligations. -/
theorem paperXiF_certificate_q_le_hull_of_obligations
    (L : ThetaLinkActual O P C3)
    (S : PaperXiFThetaLinkObligations O P C3 L) :
    (paperXiFResult_of_obligations L S).certificate.qSigned ≤
      (paperXiFResult_of_obligations L S).certificate.hull.hullVolume :=
  (paperXiFResult_of_obligations L S).certificate_q_le_hull

/-- cTheta lower bound from the exact obligations. -/
theorem paperXiF_cTheta_lowerBound_of_obligations
    (L : ThetaLinkActual O P C3)
    (S : PaperXiFThetaLinkObligations O P C3 L) {cTheta : Real}
    (hc : P.signedHullLogVolume ≤
      cTheta * |Real.log (paperQParameter C3)|) :
    -1 ≤ cTheta :=
  by
    simpa [paperXiFResult_of_obligations] using
      (paperXiFResult_of_obligations L S).cTheta_lowerBound cTheta hc

end Proof
end XiFPaper
end LeanFormal.IUT
