import tmp.sheaf.xif.PaperQPilotObject
import tmp.sheaf.xif.PaperSignedHull
import tmp.sheaf.xif.PaperQPilotLogVolume
import tmp.sheaf.xif.PaperXiFInclusion
import tmp.sheaf.xif.PaperCertificate
import tmp.sheaf.xif.PaperOModuleLayer

/-!
# Paper-level xi-f assembly and compile gate

This file imports paper-level modules only. It does NOT import the
value-layer surrogate modules (`SourceXiFConstruction`, `XiFScaling`,
`XiFContraction`, `XiFComparisonData`, `XiFCertificate`), and it does not
use `sourceQPilotPoint`/`sourceThetaHullLogVolume` for the paper target.

## What is assembled

From a `PaperXiFSourceLink` plus its explicit `link_identification` proof,
we form the paper-level `PaperXiFInclusion` and its `Cor312ComparisonData`.
The `PaperCertificate` consumer then yields `Cor312Conclusion` from actual
`FiniteStepXILinkEvidence` (IPL/SHE/APT evidence carried by the structure).

## Exact remaining source obligations

`PaperQPilotObject` fields `paper_strip_identification`,
`paper_lineBundle_identification`, `paper_logKummer_identification`,
`paper_qPilot_log_identification`; `PaperXiFSourceLink.link_identification`
and `link_implies_inclusion`; `PaperSignedHull.hull_logVolume_eq_average`
and the IQ/compactness data. These are fields of the source structures, not
axioms proved here. No inhabitant of `PaperQPilotObject`, `PaperSignedHull`,
or `PaperXiFSourceLink` is asserted.

## Paper compile gate (individual exit evidence recorded in the task report)

PaperQPilotObject.lean          EXIT 0
PaperQPilotLogVolume.lean        EXIT 0
PaperSignedHull.lean             EXIT 0
PaperXiFInclusion.lean           EXIT 0
PaperCertificate.lean            EXIT 0
PaperOModuleLayer.lean           EXIT 0
PaperAssembly.lean               EXIT 0

Command: lake env lean -j1 -R D:/lean -o <build>/<file>.olean <file>.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.N8Closure.SourcePilotRegion

universe ua uv upi umon ui uL uC uG uX uLabel

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]

/-- The paper comparison card assembled from a `PaperXiFInclusion`: its
q-pilot log-volume is the actual object scalar, its hull scalar is the paper
signed hull volume, and its xi-f membership is the paper inclusion. -/
def paperComparisonData
    {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
    {P : PaperSignedHull X label}
    {C3 : SourcePilotRegionData (l := l) (V := V) I}
    (J : PaperXiFInclusion O P C3) : Cor312ComparisonData where
  thetaHullLogVolume := P.signedHullLogVolume
  qPilotLogVolume := O.qPilotLogVolume
  qPilot_mem_ray := J.qPilot_mem_ray
  qParameter := paperQParameter C3
  qParameter_pos := paperQParameter_pos C3
  qParameter_log_ne_zero := paperQParameter_log_ne_zero C3
  qPilotLogVolume_eq := J.qPilotLogVolume_eq_neg_abs_qParameter

@[simp] theorem paperComparisonData_thetaHull
    {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
    {P : PaperSignedHull X label}
    {C3 : SourcePilotRegionData (l := l) (V := V) I}
    (J : PaperXiFInclusion O P C3) :
    (paperComparisonData J).thetaHullLogVolume = P.signedHullLogVolume := rfl

@[simp] theorem paperComparisonData_qPilot
    {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
    {P : PaperSignedHull X label}
    {C3 : SourcePilotRegionData (l := l) (V := V) I}
    (J : PaperXiFInclusion O P C3) :
    (paperComparisonData J).qPilotLogVolume = O.qPilotLogVolume := rfl

/-- The paper certificate input assembled from the paper xi-f inclusion. -/
def paperXiFInput
    {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
    {P : PaperSignedHull X label}
    {C3 : SourcePilotRegionData (l := l) (V := V) I}
    (J : PaperXiFInclusion O P C3) : PaperXiFInput P where
  data := paperComparisonData J
  theta_eq := rfl

/-- The paper xi-f membership exposed by the assembly: the actual q-pilot
scalar lies in the signed hull ray. -/
theorem paperAssembly_qPilot_mem_ray
    {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
    {P : PaperSignedHull X label}
    {C3 : SourcePilotRegionData (l := l) (V := V) I}
    (J : PaperXiFInclusion O P C3) :
    O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume :=
  J.qPilot_mem_ray

/-- **Conditioned paper-level xi-f assembly.** Given the actual
`PaperXiFSourceLink`, a proof of its explicit link identification, and actual
finite IPL/SHE/APT link evidence, the paper certificate yields
`Cor312Conclusion` via the signed certificate consumer.

No inhabitant of `PaperXiFSourceLink` is asserted; the link and its
identification are inputs. This is not the value-layer surrogate. -/
theorem paperAssembly_cor312Conclusion
    {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
    {P : PaperSignedHull X label}
    {C3 : SourcePilotRegionData (l := l) (V := V) I}
    [Nonempty label]
    (link : PaperXiFSourceLink O P C3)
    (link_holds : link.link_identification)
    (links : FiniteStepXILinkEvidence
      (paperCertificate (I := paperXiFInput
        (⟨link, link_holds⟩ : PaperXiFInclusion O P C3))).toStepXIFiniteCertificate) :
    Cor312Conclusion
      ((paperCertificate (I := paperXiFInput
        (⟨link, link_holds⟩ : PaperXiFInclusion O P C3))).toContract
        (paperSignedLinkEvidence
          (I := paperXiFInput
            (⟨link, link_holds⟩ : PaperXiFInclusion O P C3)) links)) :=
  paperCor312Conclusion
    (I := paperXiFInput
      (⟨link, link_holds⟩ : PaperXiFInclusion O P C3)) links

/-- Direct certificate q <= theta conclusion from the same conditioned paper
assembly (no finite link evidence needed). -/
theorem paperAssembly_q_le_theta
    {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
    {P : PaperSignedHull X label}
    {C3 : SourcePilotRegionData (l := l) (V := V) I}
    [Nonempty label]
    (link : PaperXiFSourceLink O P C3)
    (link_holds : link.link_identification) :
    (paperCertificate (I := paperXiFInput
      (⟨link, link_holds⟩ : PaperXiFInclusion O P C3))).qSigned ≤
      (paperCertificate (I := paperXiFInput
      (⟨link, link_holds⟩ : PaperXiFInclusion O P C3))).thetaSigned :=
  paperCertificate_q_le_theta
    (I := paperXiFInput
      (⟨link, link_holds⟩ : PaperXiFInclusion O P C3))

end LeanFormal.IUT.XiFPaper

end
