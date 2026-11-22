import tmp.sheaf.xif.paper.S2706DirectHcompActual
import tmp.sheaf.xif.paper.S2708MultiPlaceQPilotActual
import tmp.sheaf.xif.paper.PaperQPilotObjectConcreteActual
import tmp.sheaf.xif.paper.ConcreteThetaLinkSourceActual

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2714HcompTransferActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.XiFPaper.S2706DirectHcompActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual

universe ua uv upi umon ui uL uC uG uX uLabel

/-- Transfer the concrete hcomp from `paperQPilotObjectConcrete` to the
multi-place migrated object.  Both q-pilot scalars are
`sourceQPilotSignedLog I.initial`, so `concreteSourceComparison` is
definitionally the same inequality after rewriting the scalar fields. -/
theorem S2714_hcomp_multi_transfer
    {l : PrimeGeFive} {V : Type}
    {I : OriginalInput.{0, 0, 0, 0, 0} l V}
    {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
    {G : Type uG} [Group G] [TopologicalSpace G]
    {envStrip : FPrimeStrip V}
    {X : Type uX} {label : Type uLabel} [Fintype label]
    (P : PaperSignedHull X label)
    (D : MultiPlaceQPilotDonor I)
    (h : concreteSourceComparison
      (paperQPilotObjectConcrete (I := I)) P) :
    concreteSourceComparison
      (paperQPilotObject_multi (paperQPilotObjectConcrete (I := I)) D) P := by
  unfold concreteSourceComparison at h ⊢
  simpa [paperQPilotObject_multi_qPilotLogVolume,
    paperQPilotLogVolume_multi_eq_sourceQPilotSignedLog,
    paperQPilotObjectConcrete_qPilotLogVolume] using h

/-- The same transfer applied to the concrete S2706 hcomp at the S2696 source data. -/
theorem S2714_hcomp_multi_of_direct
    {l : PrimeGeFive}
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {X : Type uX} {label : Type uLabel} [Fintype label]
    (P : PaperSignedHull X label)
    (hP : P.procession.average = 2 * Real.log 5)
    (D : MultiPlaceQPilotDonor
      (S2706I R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat)) :
    concreteSourceComparison
      (paperQPilotObject_multi
        (paperQPilotObjectConcrete (I :=
          S2706I R redCompat hredCompat torCompat htorCompat orbCompat
            horbCompat secCompat hsecCompat cusCompat hcusCompat)) D) P :=
  S2714_hcomp_multi_transfer P D
    (S2706_directHcomp R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat P hP)

#check S2714_hcomp_multi_transfer
#check S2714_hcomp_multi_of_direct
#print axioms S2714_hcomp_multi_of_direct

end LeanFormal.IUT.XiFPaper.S2714HcompTransferActualAdapted
end
