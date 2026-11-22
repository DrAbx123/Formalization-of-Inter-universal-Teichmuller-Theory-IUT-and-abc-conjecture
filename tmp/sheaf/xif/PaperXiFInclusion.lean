import tmp.sheaf.xif.PaperQPilotObject
import tmp.sheaf.xif.PaperQPilotLogVolume
import tmp.sheaf.xif.PaperSignedHull
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-! # Paper-level xi-f inclusion from the actual q-pilot/hull link

This file starts from the actual paper-level objects:
* PaperQPilotObject: the actual source q-pilot strip anchor, one-column
  arithmetic holomorphic structure, reduced arithmetic vector-bundle carrier,
  and reduced Kummer arrow interface; its paper_*_identification fields are
  exact missing source obligations;
* PaperSignedHull: the paper-level ambient IQ hull interface, finite procession
  hull data, and paper signed hull log-volume -|log Theta|;
* PaperQPilotLogVolume: the actual source-completion q scalar signed log.

It does NOT use the value-layer theta-label-1 surrogate, sourceThetaHullLogVolume,
or the value-layer XiFComparisonData.

Exact missing source link (kept as fields, not axioms):
1. source q-pilot paper identifications (strip, arithmetic line bundle,
   log-Kummer representation, q-pilot log normalization);
2. qPilot.qPilotLogVolume = paperQPilotLogVolume C3 (the object scalar is the
   actual paper q-pilot scalar);
3. link_identification: the actual paper Theta-link/link identification
   proposition;
4. link_implies_inclusion: the exact missing paper xi-f link/log-volume
   comparison producing membership in R_{<= -|log Theta|}.

No inhabitant of PaperXiFSourceLink is asserted. The inclusion theorem below is
conditional on the explicit link identification. No sorry/axiom/toy is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT
namespace XiFPaper

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

/-- The actual source-completion q parameter of C3, as a positive real norm. -/
noncomputable def paperQParameter
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Real :=
  ‖C3.q.q‖

theorem paperQParameter_pos
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    0 < paperQParameter C3 := by
  unfold paperQParameter
  exact ArithmeticQPilotLogVolume.qNorm_pos C3.q

theorem paperQParameter_log_ne_zero
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    Real.log (paperQParameter C3) ≠ 0 := by
  unfold paperQParameter
  exact ne_of_lt (ArithmeticQPilotLogVolume.localSignedLog_neg C3.q)

/-- The paper q-pilot scalar is -|log q| for the actual completion q parameter. -/
theorem paperQPilotLogVolume_eq_neg_abs_paperQParameter
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    paperQPilotLogVolume C3 = -|Real.log (paperQParameter C3)| := by
  rw [paperQPilotLogVolume_eq_log_norm]
  unfold paperQParameter
  have hneg : Real.log ‖C3.q.q‖ < 0 :=
    ArithmeticQPilotLogVolume.localSignedLog_neg C3.q
  rw [abs_of_neg hneg, neg_neg]

/-- The exact source link data needed for the paper xi-f inclusion. Every
identification field is an obligation surface; the structure has no asserted
inhabitant. -/
structure PaperXiFSourceLink
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I) where
  /-- Source q-pilot paper identifications (all currently obligations). -/
  source_identifications :
    O.paper_strip_identification ∧
    O.paper_lineBundle_identification ∧
    O.paper_logKummer_identification ∧
    O.paper_qPilot_log_identification
  /-- Missing paper q-pilot log normalization: the object scalar is the actual
  source completion q scalar. -/
  qPilotLogVolume_eq_paper :
    O.qPilotLogVolume = paperQPilotLogVolume C3
  /-- The actual paper Theta-link/link identification proposition. -/
  link_identification : Prop
  /-- Exact missing paper xi-f comparison: the link identification gives
  membership in the signed hull ray. This is the source theorem not constructed
  here; it is not replaced by a hull-sup pointwise inequality. -/
  link_implies_inclusion :
    link_identification →
      O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume

/-- Paper-level xi-f inclusion data: a source link together with a proof that
its explicit link identification holds. -/
structure PaperXiFInclusion
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I) where
  link : PaperXiFSourceLink O P C3
  link_holds : link.link_identification

namespace PaperXiFInclusion

variable {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
variable {P : PaperSignedHull X label}
variable {C3 : SourcePilotRegionData (l := l) (V := V) I}

/-- The paper-level xi-f membership: -|log q| lies in R_{<= -|log Theta|}.
This is derived from the explicit link identification, not from a value-layer
hull-sup or from the theta-label-1 surrogate. -/
theorem qPilot_mem_ray (J : PaperXiFInclusion O P C3) :
    O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume :=
  J.link.link_implies_inclusion J.link_holds

/-- The paper-level xi-f inequality. -/
theorem qPilot_le_signedHull (J : PaperXiFInclusion O P C3) :
    O.qPilotLogVolume ≤ P.signedHullLogVolume :=
  (mem_hullLogVolumeRay_iff).mp J.qPilot_mem_ray

/-- The object scalar is the actual paper q-pilot scalar under the explicit
paper identification field. -/
theorem qPilotLogVolume_eq_paper (J : PaperXiFInclusion O P C3) :
    O.qPilotLogVolume = paperQPilotLogVolume C3 :=
  J.link.qPilotLogVolume_eq_paper

/-- The object scalar is -|log q| for the actual completion q parameter. -/
theorem qPilotLogVolume_eq_neg_abs_qParameter (J : PaperXiFInclusion O P C3) :
    O.qPilotLogVolume = -|Real.log (paperQParameter C3)| := by
  rw [J.qPilotLogVolume_eq_paper, paperQPilotLogVolume_eq_neg_abs_paperQParameter]

end PaperXiFInclusion

end XiFPaper
end LeanFormal.IUT
