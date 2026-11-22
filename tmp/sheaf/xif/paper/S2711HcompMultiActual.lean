import tmp.sheaf.xif.paper.S2708MultiPlaceQPilotActual
import tmp.sheaf.xif.paper.S2706DirectHcompActual

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2711HcompMultiActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual

universe ua uv upi umon ui uL uC uG uX uLabel

/-- The migrated multi-place q-pilot object keeps the scalar
`paperQPilotLogVolume_multi`, which is exactly `-sourceBadQAbsLog`. -/
theorem S2711_multi_qPilotLogVolume
    {l : PrimeGeFive} {V : Type uv}
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
    {G : Type uG} [Group G] [TopologicalSpace G]
    {envStrip : FPrimeStrip V}
    (O : PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
      I G envStrip)
    (D : MultiPlaceQPilotDonor I) :
    (paperQPilotObject_multi O D).qPilotLogVolume =
      -sourceBadQAbsLog I.initial :=
  paperQPilotLogVolume_multi_eq_neg_sourceBadQAbsLog D

/-- Direct hcomp for the multi-place migrated q-pilot object: the concrete
source comparison holds for any signed hull with raw average `2 log 5`, as
soon as the source bad-q absolute log is above `2 log 5`. -/
theorem S2711_hcomp_multi
    {l : PrimeGeFive} {V : Type uv}
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
    {G : Type uG} [Group G] [TopologicalSpace G]
    {envStrip : FPrimeStrip V}
    (O : PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
      I G envStrip)
    (D : MultiPlaceQPilotDonor I)
    {X : Type uX} {label : Type uLabel} [Fintype label]
    (P : PaperSignedHull X label)
    (hP : P.procession.average = 2 * Real.log 5)
    (hbad : 2 * Real.log 5 < sourceBadQAbsLog I.initial) :
    concreteSourceComparison (paperQPilotObject_multi O D) P := by
  unfold concreteSourceComparison
  rw [paperQPilotObject_multi_qPilotLogVolume,
    paperQPilotLogVolume_multi_eq_neg_sourceBadQAbsLog, hP]
  linarith

#check S2711_multi_qPilotLogVolume
#check S2711_hcomp_multi
#print axioms S2711_hcomp_multi

end LeanFormal.IUT.XiFPaper.S2711HcompMultiActual
end
