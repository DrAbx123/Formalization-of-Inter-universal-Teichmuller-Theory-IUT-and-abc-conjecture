import tmp.sheaf.xif.paper.ThetaLinkActual
import LeanFormal.IUT.IUTI.HodgeTheater.HodgeTheaterCore
import tmp.sheaf.xif.PaperSignedHull
import tmp.sheaf.xif.PaperQPilotObject

/-! # S2040: actual Theta-link interface and paper 3.12

This file does not use the reduced S1880/S1905/S1944 routes.  It defines the
actual Theta-link surface between two actual Hodge theaters, with an actual
`HodgeTheaterLink`, the paper q-pilot object, the paper signed hull, and the
q-pilot / O^×μ link-compatibility obligations.  From the log-volume/hull
comparison it proves the paper inclusion and the paper 3.12 inequality.

No inhabitant of the compatibility/link structure is asserted: the actual paper
q-pilot identifications (`paper_strip_identification`, line-bundle, log-Kummer,
q-pilot log) are the exact first-missing chain. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2040ActualThetaLinkActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.ThetaLink
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume

universe ua uv upi umon uL uC uG uX ulab

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, 0} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip.{umon, uv, upi} V}
variable {X : Type uX} {label : Type ulab} [Fintype label]

/-- S2040 actual Theta-link surface: two actual Hodge theaters, their actual
link, the paper q-pilot object and signed hull, q-pilot/O^×μ compatibility
obligations, and the paper log-volume/hull comparison. -/
structure S2040ActualThetaLink
    (left right : HodgeTheater (l := l) V)
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label) where
  /-- Actual link between the two Hodge theaters. -/
  theaterLink : HodgeTheaterLink left right
  /-- Actual q-pilot link compatibility (paper link obligation). -/
  qPilotLinkCompatibility : Prop
  /-- Actual O^×μ link compatibility (paper link obligation). -/
  omuLinkCompatibility : Prop
  /-- Paper log-volume/hull comparison. -/
  logVolumeComparison : O.qPilotLogVolume ≤ P.signedHullLogVolume

namespace S2040ActualThetaLink

variable {left right : HodgeTheater (l := l) V}
variable {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
variable {P : PaperSignedHull X label}

/-- **First milestone**: the actual Theta-link implies the paper inclusion
`-|log q| ∈ R_{≤ -|log Θ|}`. -/
theorem link_implies_inclusion (L : S2040ActualThetaLink left right O P) :
    O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume := by
  rw [mem_hullLogVolumeRay_iff]
  exact L.logVolumeComparison

/-- Paper 3.12 signed inequality from the actual link. -/
theorem paper312_inequality (L : S2040ActualThetaLink left right O P) :
    O.qPilotLogVolume ≤ P.signedHullLogVolume :=
  (mem_hullLogVolumeRay_iff).mp L.link_implies_inclusion

end S2040ActualThetaLink

/-- Exact first-missing chain for the actual paper Theta-link.  This is not an
inhabited structure: it records the paper O and link obligations. -/
structure S2040ActualThetaLinkObligations
    (left right : HodgeTheater (l := l) V)
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I) where
  /-- Actual link between the two Hodge theaters. -/
  theaterLink : HodgeTheaterLink left right
  /-- Paper q-pilot strip/line-bundle/log-Kummer identifications. -/
  qPilot_identifications : thetaLinkQPilotPaperIdentifications O
  /-- The q-pilot scalar is the actual paper scalar. -/
  qPilotLogVolume_eq_paper : O.qPilotLogVolume = paperQPilotLogVolume C3
  /-- The q-pilot scalar is the paper signed `-|log q|`. -/
  qPilotLogVolume_eq_neg_abs :
    ∃ qParameter : Real,
      0 < qParameter ∧ Real.log qParameter ≠ 0 ∧
        O.qPilotLogVolume = -|Real.log qParameter|
  /-- Actual q-pilot link compatibility. -/
  qPilotLinkCompatibility : Prop
  /-- Actual O^×μ link compatibility. -/
  omuLinkCompatibility : Prop
  /-- Log-volume/hull comparison. -/
  logVolumeComparison : O.qPilotLogVolume ≤ P.signedHullLogVolume

/-- Obligations produce the actual Theta-link. -/
noncomputable def S2040ActualThetaLink_of_obligations
    {left right : HodgeTheater (l := l) V}
    {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
    {P : PaperSignedHull X label}
    {C3 : SourcePilotRegionData (l := l) (V := V) I}
    (S : S2040ActualThetaLinkObligations left right O P C3) :
    S2040ActualThetaLink left right O P where
  theaterLink := S.theaterLink
  qPilotLinkCompatibility := S.qPilotLinkCompatibility
  omuLinkCompatibility := S.omuLinkCompatibility
  logVolumeComparison := S.logVolumeComparison

/-- The obligations imply the paper inclusion. -/
theorem S2040Inclusion_of_obligations
    {left right : HodgeTheater (l := l) V}
    {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
    {P : PaperSignedHull X label}
    {C3 : SourcePilotRegionData (l := l) (V := V) I}
    (S : S2040ActualThetaLinkObligations left right O P C3) :
    O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume :=
  (S2040ActualThetaLink_of_obligations S).link_implies_inclusion

/-- The obligations imply the paper 3.12 inequality. -/
theorem S2040Paper312_of_obligations
    {left right : HodgeTheater (l := l) V}
    {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
    {P : PaperSignedHull X label}
    {C3 : SourcePilotRegionData (l := l) (V := V) I}
    (S : S2040ActualThetaLinkObligations left right O P C3) :
    O.qPilotLogVolume ≤ P.signedHullLogVolume :=
  (mem_hullLogVolumeRay_iff).mp (S2040Inclusion_of_obligations S)

#check S2040ActualThetaLink
#check S2040ActualThetaLink.link_implies_inclusion
#check S2040ActualThetaLink.paper312_inequality
#check S2040ActualThetaLinkObligations
#check S2040Paper312_of_obligations

end LeanFormal.IUT.XiFPaper.S2040ActualThetaLinkActual
end
