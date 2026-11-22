import tmp.sheaf.xif.paper.QPilotObjectActual
import tmp.sheaf.xif.paper.QPilotIdentificationActual
import tmp.sheaf.xif.paper.ThetaHullActual
import tmp.sheaf.xif.paper.ThetaHullIdentificationActual
import tmp.sheaf.xif.paper.SignedHullLogActual
import tmp.sheaf.xif.paper.SignedHullNormalizationActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.OModuleActual
import tmp.sheaf.xif.paper.IndeterminaciesActual
import tmp.sheaf.xif.paper.SHELandingActual
import tmp.sheaf.xif.paper.IPLAPTActual
import tmp.sheaf.xif.paper.ThetaLinkLogKummerActual
import tmp.sheaf.xif.paper.ThetaLinkActual
import tmp.sheaf.xif.paper.PaperXiFProof
import tmp.sheaf.xif.paper.PaperXiFUnconditional
import tmp.sheaf.xif.PaperXiFInclusion
import tmp.sheaf.xif.PaperCertificate
import tmp.sheaf.xif.paper.PaperXiFTheorem

/-! # Paper-level actual module assembly and compile gate

STATUS: paper-level assembly/consumer layer. No value-layer surrogate, no
PUnit/Unit, no True, no axiom, no sorry, no asserted inhabitant.

## Actual modules consumed

The following actual paper-level modules are imported and checked at the gate:
* QPilotObjectActual, QPilotIdentificationActual;
* ThetaHullActual, ThetaHullIdentificationActual;
* SignedHullLogActual, SignedHullNormalizationActual;
* DeterminantLogVolumeActual;
* OModuleActual;
* IndeterminaciesActual;
* SHELandingActual (the current SHE carrier; the expected SHEOutputActual
  module is declared below and will replace/add the output specialization);
* IPLAPTActual;
* ThetaLinkLogKummerActual;
* ThetaLinkActual;
* PaperXiFProof, PaperXiFUnconditional, PaperXiFInclusion, PaperXiFTheorem;
* PaperCertificate.

## Expected paper modules/names

The batch is expected to provide (current tree state noted):
* SHEOutputActual: actual SHE output specialization. Not present in this tree
  at assembly time; SHELandingActual is used as the current actual carrier.
* PaperXiFUnconditional: present; provides PaperUnconditionalData and the
  conditional paper xi-f theorem.
* ThetaLinkLogKummerActual: present; actual Theta-link/log-Kummer comparison
  layer with q-pilot/signed-hull obligations.
* QPilotIdentificationActual: present; actual q-pilot strip/one-column/
  log-Kummer/(1,0) identifications.
* ThetaHullIdentificationActual: present; actual C6 IQ hull/procession/
  compactness interface and paper normalization obligations.
* SignedHullNormalizationActual: present; determinant/tensor normalization.
* DeterminantLogVolumeActual: present; actual line-bundle determinant/local
  log-volume layer.
* PaperCertificate: present; signed finite certificate consumer.

## Consumer content

This file:
1. exposes the conditional paper xi-f inequality from PaperUnconditionalData;
2. exposes the signed certificate q_le_hull slot from the actual Theta-link
   data and PaperXiFProof;
3. exposes the cTheta lower bound consumer;
4. records the unconditional target as a proposition, not a proved theorem;
5. provides a #check gate for every actual module declaration used.

No inhabitant of PaperUnconditionalData, ThetaLinkActual, or the unconditional
target is constructed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT
namespace XiFPaper
namespace AssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.Proof
open LeanFormal.IUT.XiFPaper.ThetaLink
open LeanFormal.IUT.N8Closure.PaperQPilotIdentificationActual
open LeanFormal.IUT.XiFPaperThetaHullIdentification
open LeanFormal.IUT.SignedHullNormalizationActual
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHELandingActual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.N8C6.PaperNormalizedVolume

universe ua uv upi umon ui uL uC uG uX uLabel uK uM uP uC3 uD3 uOut1 uOut2

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable [Nonempty label]
variable {v : V}
variable {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
variable {P : PaperSignedHull X label}
variable {C3 : SourcePilotRegionData (l := l) (V := V) I}

/-! ## 1. Conditional paper xi-f consumer from the actual unconditional data -/

/-- Conditional paper xi-f inequality from the actual PaperUnconditionalData.
The data records the actual q-pilot object, signed hull, source link, Ind action,
IPL/Theta-link, and O-module layer. The link identification is an explicit field
of the data, not an axiom. -/
theorem paperXiF_assembly_conditional
    {k : Type uK} [Field k] [NumberField k] {r : Nat}
    {selected : Finset (NumberField.FinitePlace k)}
    (D : PaperUnconditionalData (l := l) (V := V) (Label := Label)
      (Choice := Choice) (I := I) (G := G) (envStrip := envStrip)
      (X := X) (label := label) (k := k) (r := r) (selected := selected)
      v O P C3) :
    O.qPilotLogVolume ≤ P.signedHullLogVolume :=
  PaperUnconditionalData.qPilot_le_signedHull D

/-- Conditional paper xi-f membership from the actual unconditional data. -/
theorem paperXiF_assembly_membership
    {k : Type uK} [Field k] [NumberField k] {r : Nat}
    {selected : Finset (NumberField.FinitePlace k)}
    (D : PaperUnconditionalData (l := l) (V := V) (Label := Label)
      (Choice := Choice) (I := I) (G := G) (envStrip := envStrip)
      (X := X) (label := label) (k := k) (r := r) (selected := selected)
      v O P C3) :
    O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume :=
  PaperUnconditionalData.qPilot_mem_ray D

/-- Conditional paper q-pilot scalar identification from the actual data. -/
theorem paperXiF_assembly_qPilot_eq_paper
    {k : Type uK} [Field k] [NumberField k] {r : Nat}
    {selected : Finset (NumberField.FinitePlace k)}
    (D : PaperUnconditionalData (l := l) (V := V) (Label := Label)
      (Choice := Choice) (I := I) (G := G) (envStrip := envStrip)
      (X := X) (label := label) (k := k) (r := r) (selected := selected)
      v O P C3) :
    O.qPilotLogVolume = paperQPilotLogVolume C3 :=
  PaperUnconditionalData.qPilotLogVolume_eq_paper D

/-! ## 2. Signed certificate consumer from the actual Theta-link -/

/-- Signed certificate q_le_hull slot from the actual Theta-link and an explicit
link identification. This consumes PaperXiFProof and PaperCertificate; no
inhabitant of ThetaLinkActual is asserted. -/
theorem paperXiF_assembly_certificate_q_le_hull
    (L : ThetaLinkActual O P C3) (hlink : L.link_identification) :
    (thetaLinkCertificate O P C3 L hlink).qSigned ≤
      (thetaLinkCertificate O P C3 L hlink).hull.hullVolume :=
  thetaLinkCertificate_q_le_hull O P C3 L hlink

/-- Signed certificate q_le_theta slot from the actual Theta-link. -/
theorem paperXiF_assembly_certificate_q_le_theta
    (L : ThetaLinkActual O P C3) (hlink : L.link_identification) :
    (thetaLinkCertificate O P C3 L hlink).qSigned ≤
      (thetaLinkCertificate O P C3 L hlink).thetaSigned :=
  thetaLinkCertificate_q_le_theta O P C3 L hlink

/-- cTheta lower bound from the actual Theta-link and paper Theta comparison. -/
theorem paperXiF_assembly_cTheta_lowerBound
    (L : ThetaLinkActual O P C3) (hlink : L.link_identification)
    {cTheta : Real}
    (hc : P.signedHullLogVolume ≤
      cTheta * |Real.log (paperQParameter C3)|) :
    -1 ≤ cTheta :=
  paperXiF_cTheta_lowerBound_of_obligations L
    (by
      exact {
        qPilot_identifications := L.qPilot_identifications
        qPilotLogVolume_eq_paper := L.qPilotLogVolume_eq_paper
        qPilotLogVolume_eq_neg_abs := L.qPilotLogVolume_eq_neg_abs
        link_identification := hlink
        link_implies_inclusion := L.link_implies_inclusion
      }) hc

/-! ## 3. Paper-level unconditional target: proposition only

The unconditional target is the existence of the actual paper-level data
package. It is not proved here and no inhabitant is manufactured. -/

/-- The unconditional paper xi-f target, as an actual proposition. This is the
unconditional consumer surface; it is not asserted. -/
def PaperXiFActualTarget
    (v : V) (k : Type uK) [Field k] [NumberField k] (r : Nat)
    (selected : Finset (NumberField.FinitePlace k)) : Prop :=
  PaperXiFUnconditionalTarget (l := l) (V := V) (Label := Label)
    (Choice := Choice) (I := I) (G := G) (envStrip := envStrip)
    (X := X) (label := label) (k := k) (r := r) (selected := selected) v

/-- The conditioned theorem surface: PaperXiFActualTarget would yield the paper
xi-f inequality. This is a conditional implication, not an unconditional
assertion. -/
theorem paperXiF_assembly_of_target
    (h : PaperXiFActualTarget (l := l) (V := V) (Label := Label)
      (Choice := Choice) (I := I) (G := G) (envStrip := envStrip)
      (X := X) (label := label) (k := k) (r := r) (selected := selected)
      v) :
    ∃ (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip),
      ∃ (P : PaperSignedHull X label),
      ∃ (C3 : SourcePilotRegionData (l := l) (V := V) I),
        O.qPilotLogVolume ≤ P.signedHullLogVolume := by
  rcases h with ⟨O, P, C3, ⟨D⟩⟩
  exact ⟨O, P, C3, PaperUnconditionalData.qPilot_le_signedHull D⟩

/-! ## 4. Composed PaperXiFResult consumer from the actual Theta-link -/

/-- The composed paper xi-f result from the actual Theta-link and an explicit
link identification. This exposes scalar xi-f, the signed certificate, and the
cTheta bound in one PaperXiFResult without asserting an inhabitant. -/
def paperXiF_assembly_result
    (L : ThetaLinkActual O P C3) (hlink : L.link_identification) :
    PaperXiFResult O P C3 :=
  paperXiFResultOfThetaLink L hlink

/-- Scalar paper xi-f extracted from the composed result. -/
theorem paperXiF_assembly_result_xi_f
    (L : ThetaLinkActual O P C3) (hlink : L.link_identification) :
    paperXiF (paperQParameter C3) P.signedHullLogVolume :=
  (paperXiF_assembly_result L hlink).xi_f

/-- Signed certificate q_le_hull slot extracted from the composed result. -/
theorem paperXiF_assembly_result_q_le_hull
    (L : ThetaLinkActual O P C3) (hlink : L.link_identification) :
    (paperXiF_assembly_result L hlink).certificate.qSigned ≤
      (paperXiF_assembly_result L hlink).certificate.hull.hullVolume :=
  (paperXiF_assembly_result L hlink).certificate_q_le_hull

/-- cTheta lower bound extracted from the composed result. -/
theorem paperXiF_assembly_result_cTheta
    (L : ThetaLinkActual O P C3) (hlink : L.link_identification)
    {cTheta : Real}
    (hc : P.signedHullLogVolume ≤
      cTheta * |Real.log (paperQParameter C3)|) :
    -1 ≤ cTheta :=
  (paperXiF_assembly_result L hlink).cTheta_lowerBound cTheta hc

/-! ## 5. Compile gate checks

These #check commands are the paper-level gate: every actual module used above
is required to expose its main declaration. They do not assert inhabitants. -/

#check LeanFormal.IUT.N8Closure.PaperQPilotIdentificationActual.QPilotIdentificationActual
#check LeanFormal.IUT.XiFPaperThetaHullIdentification.ThetaHullIdentificationActual
#check LeanFormal.IUT.SignedHullNormalizationActual.NormalizedHullData
#check LeanFormal.IUT.SignedHullNormalizationActual.actualNormalizedHullData
#check LeanFormal.IUT.PaperDeterminantLogVolume.PaperDeterminantLogVolumeData
#check LeanFormal.IUT.PaperDeterminantLogVolume.actualDeterminantLogVolumeData
#check LeanFormal.IUT.Theorem311Source.OriginalInput.ThetaLinkLogKummerActual
#check LeanFormal.IUT.Theorem311Source.SHELandingActual.Output
#check LeanFormal.IUT.Theorem311Source.SHELandingActual.completionSHELanding_nonGate
#check LeanFormal.IUT.XiFPaper.PaperXiFUnconditionalTarget
#check LeanFormal.IUT.XiFPaper.PaperUnconditionalData
#check LeanFormal.IUT.XiFPaper.PaperXiFInclusion
#check LeanFormal.IUT.paperCertificate
#check LeanFormal.IUT.StepXIFiniteCertificateSigned
#check LeanFormal.IUT.XiFPaper.ThetaLink.thetaLinkCertificate
#check LeanFormal.IUT.XiFPaper.ThetaLink.thetaLinkCertificate_q_le_hull
#check LeanFormal.IUT.XiFPaper.ThetaLink.thetaLinkCertificate_q_le_theta
#check LeanFormal.IUT.XiFPaper.Proof.paperXiF_cTheta_lowerBound_of_obligations

end AssemblyActual
end XiFPaper
end LeanFormal.IUT
