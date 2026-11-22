import tmp.sheaf.xif.paper.S2704S2696SourceDataActual
import tmp.sheaf.xif.paper.S1487OQPilotScalarEqualityActual
import tmp.sheaf.xif.paper.PaperQPilotObjectConcreteActual
import tmp.sheaf.xif.paper.ConcreteThetaLinkSourceActual
import tmp.sheaf.xif.PaperSignedHull

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2706DirectHcompActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2704S2696SourceDataActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual

universe uX uLabel
variable {l : PrimeGeFive}

/-- The S2696 source datum over the concrete Gaussian arithmetic. -/
noncomputable abbrev S2706SourceData
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    SourceDefinition31Data l :=
  S2696SourceData l R redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat

/-- The original input over the concrete finite-prime carrier whose `initial`
is exactly the S2696 source datum. -/
noncomputable def S2706I
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    OriginalInput l (FinitePrimePlace 2 7) :=
  S1487OriginalInput
    (S2706SourceData R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)

theorem S2706I_initial
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (S2706I R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat).initial =
      S2706SourceData R redCompat hredCompat torCompat htorCompat
        orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat := rfl

theorem S2706_O_qPilotLogVolume
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (paperQPilotObjectConcrete
      (S2706I R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat)).qPilotLogVolume =
      -sourceBadQAbsLog
        (S2706SourceData R redCompat hredCompat torCompat htorCompat
          orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) := by
  rw [PaperQPilotObject.qPilotLogVolume_eq_neg_abs_sum]
  rfl

/-- Direct hcomp: for **any** signed hull `P` whose raw procession average is
`2 log 5`, the concrete source comparison against the q-pilot object of the
S2696 source datum holds.  Uses the S2704 strict lower bound
`2 log 5 < sourceBadQAbsLog`; no halign, no `OriginalInput` equality to the
native base-q data, no V=Unit packaging. -/
theorem S2706_directHcomp
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {X : Type uX} {label : Type uLabel} [Fintype label]
    (P : PaperSignedHull X label)
    (hP : P.procession.average = 2 * Real.log 5) :
    concreteSourceComparison
      (paperQPilotObjectConcrete
        (S2706I R redCompat hredCompat torCompat htorCompat orbCompat
          horbCompat secCompat hsecCompat cusCompat hcusCompat)) P := by
  unfold concreteSourceComparison
  rw [S2706_O_qPilotLogVolume R redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat, hP]
  have hlt := two_log5_lt_sourceBadQAbsLog l R redCompat hredCompat
    torCompat htorCompat orbCompat horbCompat secCompat hsecCompat
    cusCompat hcusCompat
  linarith

#check S2706I_initial
#check S2706_O_qPilotLogVolume
#check S2706_directHcomp
#print axioms S2706_O_qPilotLogVolume
#print axioms S2706_directHcomp

end LeanFormal.IUT.XiFPaper.S2706DirectHcompActual
end
