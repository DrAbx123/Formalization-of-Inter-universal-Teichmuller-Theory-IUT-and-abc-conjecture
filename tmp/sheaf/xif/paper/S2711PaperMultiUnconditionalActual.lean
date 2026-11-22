import tmp.sheaf.xif.paper.S2708MultiPlaceQPilotActual
import tmp.sheaf.xif.paper.S2706DirectHcompActual
import tmp.sheaf.xif.paper.ConcretePaperUnconditionalDataUnconditionalActual
import tmp.sheaf.xif.paper.PaperQPilotIdentificationsActual
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual
import tmp.sheaf.xif.paper.S2712MultiQConsumerActual

/-!
# S2711: paper multi-place unconditional data from the S2706 input

## Layer and consumer

Final unconditional assembly at the paper q-pilot level.  This file constructs,
from the actual objects only:

* I := S2706I R ... (the concrete S2696 source datum over the Gaussian
  arithmetic, at l = 5);
* D0 := MultiPlaceQPilotDonor.ofSource I, the actual Real-valued multi-place
  q-pilot donor whose qFamily is definitionally I.initial.reduction.qParameter;
* O_base := paperQPilotObjectConcrete I;
* O := paperQPilotObject_multi O_base D0, the migrated q-pilot object whose
  scalar is paperQPilotLogVolume_multi D0 = -sourceBadQAbsLog I.initial;
* P := unconditionalHull places tuple nu D, the normalized-Haar signed hull;
* hP : P.procession.average = 2 log 5;
* hcomp : concreteSourceComparison O P, derived from S2706_directHcomp after
  migrating O.qPilotLogVolume to the multi-place scalar;
* hqMulti : HqMulti D0 (definitional: hqMulti_holds D0).

Consumers: the paper xi-f inclusion and the Cor312 consumer through the
corrected multi-place source link (S2712MultiQConsumerActual).

## The exact object gap of the paper-faithful single-C3 PaperUnconditionalData

The direct attempt

  PaperXiFSourceLink O P (actualSignedC3 D)

with the four actual paper identifications, the actual concrete comparison as
link_identification and its actual membership implication fails exactly at the
scalar field qPilotLogVolume_eq_paper.  Verbatim Lean 4.32.2 error (line 338 of
the probe version, EXIT 1):

  Type mismatch
    paperQPilotObject_qPilotLogVolume_eq_multi
      (S2711OBase ...) (S2711Donor ...)
  has type
    (S2711OBase ...).qPilotLogVolume =
      paperQPilotLogVolume_multi (S2711Donor ...)
  but is expected to have type
    (S2711O ...).qPilotLogVolume =
      N8Closure.PaperQPilotLogVolume.paperQPilotLogVolume (actualSignedC3 D)

The expected right-hand side is the single-completion scalar
paperQPilotLogVolume C3 = localSignedLog C3.q = Real.log ‖C3.q.q‖, while the
multi-place donor supplies

  paperQPilotLogVolume_multi D0
    = - sum_{b : I.initial.badPlaces} |Real.log (qParameter b)|,

a sum over the actual bad-place index.  No single completion element can carry
that sum: a q-candidate in a completion has log norm -n * log p for one prime p
and one integer n, whereas the bad family has several independent places.  The
field qPilotLogVolume_eq_paper therefore forces the missing source-q identity
ConcreteSourceQIdentification (sourceQPilotSignedLog = localSignedLog C3.q),
which this file proves exactly (S2711_paperUnconditionalData_requires_sourceQ)
and proves sufficient (S2711PaperUnconditionalData_of_sourceQ).  It is not
inhabited by the multi donor and is not asserted.

## The corrected object

The multi-place replacement is defined and inhabited:

* PaperUnconditionalDataMulti (in this file): sourceLink is a
  MultiQPaperXiFSourceLink O P D (S2712MultiQConsumerActual) whose scalar field
  qPilotLogVolume_eq_multi is O.qPilotLogVolume = paperQPilotLogVolume_multi D;
  thetaLink is the actual self IPL/Kummer-evaluation Theta-link data;
* S2711PaperMultiUnconditionalData: the concrete instance at I, O, D0, P, with
  the four actual paper identifications, the actual comparison as
  link_identification, and hcomp as its proof;
* S2711_qPilot_le_signedHull and S2711_sourceQPilot_le_signedHull: the paper
  xi-f inequality O.qPilotLogVolume <= P.signedHullLogVolume, equivalently
  sourceQPilotSignedLog I.initial <= P.signedHullLogVolume, unconditionally
  (given R and the four Definition 3.1 compatibility propositions, exactly as
  in S2706/S2707).

No sorry, no axiom, no native_decide, no True, no fake donor, no modification of
any existing file.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2711PaperMultiUnconditionalActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual
open LeanFormal.IUT.Theorem311Source.PaperQPilotIdentificationsActual
open LeanFormal.IUT.Theorem311Source.ConcreteQPilotLogIdentificationActual
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.ConcretePaperUnconditionalDataActual
open LeanFormal.IUT.XiFPaper.ConcretePaperUnconditionalDataUnconditionalActual
open LeanFormal.IUT.XiFPaper.ConcreteSignedHullUnconditionalActual
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.XiFPaper.S2706DirectHcompActual
open LeanFormal.IUT.XiFPaper.S2704S2696SourceDataActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2712MultiQConsumerActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume

universe ua uv upi umon ui uL uC uG uX uLabel

/-- The same local high-priority procession-choice preorder as S2686, so that
all PaperQPilotObject / PaperUnconditionalData ascriptions use the instance
term of paperQPilotObjectConcrete. -/
local instance (priority := 10000) s2711ProcessionPreorder (l : PrimeGeFive) :
    Preorder (ConcreteFiniteTheorem311.ProcessionChoice l) :=
  concreteProcessionChoicePreorder l

/-! ## 1. The corrected paper data: a multi-place source link -/

/-- The multi-place replacement of PaperUnconditionalData.  The single-C3
scalar field qPilotLogVolume_eq_paper is replaced by the multi-place donor D and
the MultiQPaperXiFSourceLink scalar identification
qPilotLogVolume_eq_multi : O.qPilotLogVolume = paperQPilotLogVolume_multi D.
The remaining fields (the four paper q-pilot identifications, the explicit
link identification with its membership implication, and the actual
IPL/Kummer-evaluation Theta-link data) are unchanged. -/
structure PaperUnconditionalDataMulti
    {l : PrimeGeFive} {V : Type uv}
    {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    {G : Type uG} [Group G] [TopologicalSpace G]
    {envStrip : FPrimeStrip V}
    {X : Type uX} {label : Type uLabel} [Fintype label]
    (v : V)
    (O : PaperQPilotObject (l := l) (V := V) (Label := Label)
      (Choice := Choice) I G envStrip)
    (D : MultiPlaceQPilotDonor I)
    (P : PaperSignedHull X label) where
  /-- The multi-place source link, with the multi-place scalar field. -/
  sourceLink : MultiQPaperXiFSourceLink O P D
  /-- Its explicit link identification holds. -/
  sourceLink_holds : sourceLink.link_identification
  /-- The actual self IPL/Kummer-evaluation Theta-link data. -/
  thetaLink : PaperThetaLinkData (G := G)
    (intermediateStrip := envStrip) (gauStrip := envStrip)
    (envStrip := envStrip) (coricEnvStrip := envStrip)
    (qPilotStrip := envStrip)
    (upperLeft := envStrip) (upperRight := envStrip)
    (lowerLeft := envStrip) (lowerRight := envStrip)

namespace PaperUnconditionalDataMulti

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable {v : V}
variable {O : PaperQPilotObject (l := l) (V := V) (Label := Label)
  (Choice := Choice) I G envStrip}
variable {D : MultiPlaceQPilotDonor I}
variable {P : PaperSignedHull X label}

/-- The paper xi-f membership from the multi-place data. -/
theorem qPilot_mem_ray (M : PaperUnconditionalDataMulti v O D P) :
    O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume :=
  M.sourceLink.link_implies_inclusion M.sourceLink_holds

/-- The paper xi-f inequality q-pilot <= signed hull. -/
theorem qPilot_le_signedHull (M : PaperUnconditionalDataMulti v O D P) :
    O.qPilotLogVolume ≤ P.signedHullLogVolume :=
  (mem_hullLogVolumeRay_iff).mp M.qPilot_mem_ray

/-- The object scalar is the multi-place q-pilot volume. -/
theorem qPilotLogVolume_eq_multi (M : PaperUnconditionalDataMulti v O D P) :
    O.qPilotLogVolume = paperQPilotLogVolume_multi D :=
  M.sourceLink.qPilotLogVolume_eq_multi

/-- The object scalar is the negative source bad-q absolute log. -/
theorem qPilotLogVolume_eq_neg_sourceBadQAbsLog
    (M : PaperUnconditionalDataMulti v O D P) :
    O.qPilotLogVolume = -sourceBadQAbsLog I.initial := by
  rw [M.qPilotLogVolume_eq_multi,
    paperQPilotLogVolume_multi_eq_neg_sourceBadQAbsLog]

/-- The multi-place identification in the HqMulti orientation. -/
theorem sourceQPilotSignedLog_eq_multi
    (M : PaperUnconditionalDataMulti v O D P) :
    sourceQPilotSignedLog I.initial = paperQPilotLogVolume_multi D := by
  rw [← M.qPilotLogVolume_eq_multi]
  exact O.qPilotLogVolume_eq.symm

/-- HqMulti holds for the multi-place source link. -/
theorem hqMulti (M : PaperUnconditionalDataMulti v O D P) : HqMulti D := by
  unfold HqMulti
  exact M.sourceQPilotSignedLog_eq_multi

/-- The actual Theta-link compatibility carried by the data. -/
theorem thetaLink_compatibility (M : PaperUnconditionalDataMulti v O D P) :
    M.thetaLink.ipl.inputLink = M.thetaLink.ipl.composite ∧
      M.thetaLink.kummerEvaluation.square.domainExpression =
        M.thetaLink.kummerEvaluation.square.codomainExpression :=
  ⟨M.thetaLink.ipl_factorization, M.thetaLink.kummerEvaluation_commutes⟩

end PaperUnconditionalDataMulti

/-! ## 2. The actual S2706 input, multi donor, objects and hull -/

/-- The actual S2706 concrete input, at l = 5. -/
noncomputable abbrev S2711I
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    OriginalInput.{0, 0, 0, 0, 0} fiveLabel (FinitePrimePlace 2 7) :=
  S2706I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat

/-- The canonical multi-place donor over the actual source q-parameter family. -/
noncomputable abbrev S2711Donor
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    MultiPlaceQPilotDonor (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) :=
  MultiPlaceQPilotDonor.ofSource

/-- The concrete q-pilot object before the multi-place scalar migration. -/
noncomputable abbrev S2711OBase
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    PaperQPilotObject (l := fiveLabel) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel fiveLabel)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice fiveLabel)
      (I := S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)
      (G := ConcreteKummerGroup (l := fiveLabel))
      (envStrip := concreteQPilotStrip (l := fiveLabel)) :=
  paperQPilotObjectConcrete (l := fiveLabel) (I := S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)

/-- The migrated multi-place q-pilot object. -/
noncomputable abbrev S2711O
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    PaperQPilotObject (l := fiveLabel) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel fiveLabel)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice fiveLabel)
      (I := S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)
      (G := ConcreteKummerGroup (l := fiveLabel))
      (envStrip := concreteQPilotStrip (l := fiveLabel)) :=
  paperQPilotObject_multi (l := fiveLabel) (V := FinitePrimePlace 2 7)
    (I := S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)
    (S2711OBase R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)
    (S2711Donor R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)

/-- The unconditional normalized-Haar signed hull over the S2706 donor. -/
noncomputable abbrev S2711P
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {iota : Type} [Fintype iota] {W : iota -> Type}
    (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> W i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (nu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure nu]
    (D : SourcePilotRegionDonors (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)) :
    PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel fiveLabel.value) :=
  unconditionalHull (l := fiveLabel) (I := S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) places tuple nu D

/-! ## 3. hP: the procession average is 2 log 5 -/

theorem S2711P_average
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {iota : Type} [Fintype iota] {W : iota -> Type}
    (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> W i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (nu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure nu]
    (D : SourcePilotRegionDonors (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)) :
    (S2711P R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D).procession.average =
      2 * Real.log 5 := by
  have hproc :
      (S2711P R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D).procession =
        c3ThetaSignedProcession
          (actualSignedC3 (l := fiveLabel) (V := FinitePrimePlace 2 7)
            (I := S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) D) :=
    unconditionalPaperSignedHull_procession_eq (l := fiveLabel)
      (I := S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) places tuple D nu
  rw [hproc]
  exact signedAverage_eq_two_log5 (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) D

/-! ## 4. The multi-place scalar of O -/

/-- O is the multi-place migration of O_base: the scalars agree. -/
theorem S2711O_qPilotLogVolume_eq_base
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (S2711O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).qPilotLogVolume = (S2711OBase R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).qPilotLogVolume := by
  change paperQPilotLogVolume_multi (S2711Donor R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) =
    sourceQPilotSignedLog (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).initial
  exact paperQPilotLogVolume_multi_eq_sourceQPilotSignedLog _

/-- The source signed scalar of O. -/
theorem S2711O_qPilotLogVolume_eq_source
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (S2711O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).qPilotLogVolume =
      sourceQPilotSignedLog (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).initial :=
  (S2711O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).qPilotLogVolume_eq

/-- The multi-place scalar of O is the negative source bad-q absolute log. -/
theorem S2711O_qPilotLogVolume
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (S2711O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).qPilotLogVolume =
      -sourceBadQAbsLog (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).initial := by
  change paperQPilotLogVolume_multi (S2711Donor R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) =
    -sourceBadQAbsLog (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).initial
  exact paperQPilotLogVolume_multi_eq_neg_sourceBadQAbsLog _

/-! ## 5. hcomp from S2706_directHcomp -/

/-- The concrete source comparison for the migrated object, derived from the
S2706 direct hcomp after migrating the scalar through
paperQPilotObject_qPilotLogVolume_eq_multi. -/
theorem S2711_hcomp
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {iota : Type} [Fintype iota] {W : iota -> Type}
    (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> W i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (nu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure nu]
    (D : SourcePilotRegionDonors (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)) :
    concreteSourceComparison (S2711O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) (S2711P R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D) := by
  have hbase :
      concreteSourceComparison (S2711OBase R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)
        (S2711P R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D) :=
    S2706_directHcomp R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat (S2711P R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D)
      (S2711P_average R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D)
  have hscalar := S2711O_qPilotLogVolume_eq_base R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat
  unfold concreteSourceComparison at hbase ⊢
  rw [hscalar]
  exact hbase

/-- The paper inequality O.qPilotLogVolume <= P.signedHullLogVolume, directly
from the concrete comparison. -/
theorem S2711O_le_signedHull
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {iota : Type} [Fintype iota] {W : iota -> Type}
    (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> W i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (nu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure nu]
    (D : SourcePilotRegionDonors (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)) :
    (S2711O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).qPilotLogVolume ≤
      (S2711P R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D).signedHullLogVolume :=
  (mem_hullLogVolumeRay_iff).mp
    (concreteMembership_of_sourceComparison (S2711O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)
      (S2711P R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D) (S2711_hcomp R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D))

/-! ## 6. hqMulti -/

/-- The migrated hq: definitional in the multi-place donor. -/
theorem S2711_hqMulti
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    HqMulti (S2711Donor R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) :=
  hqMulti_holds _

/-- HqMulti in the explicit scalar orientation. -/
theorem S2711_hqMulti_eq
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    sourceQPilotSignedLog (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).initial =
      paperQPilotLogVolume_multi (S2711Donor R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) :=
  S2711_hqMulti R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat

/-! ## 7. The concrete multi-place source link and paper data -/

/-- The multi-place source link: the four actual paper identifications, the
multi-place scalar identification, the concrete source comparison as
link_identification, and its actual membership implication. -/
noncomputable def S2711MultiSourceLink
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {iota : Type} [Fintype iota] {W : iota -> Type}
    (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> W i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (nu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure nu]
    (D : SourcePilotRegionDonors (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)) :
    MultiQPaperXiFSourceLink (S2711O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)
      (S2711P R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D) (S2711Donor R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) where
  source_identifications :=
    ⟨(paperQPilotIdentificationsActual (l := fiveLabel) (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)).paper_strip,
      (paperQPilotIdentificationsActual (l := fiveLabel) (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)).paper_lineBundle,
      (paperQPilotIdentificationsActual (l := fiveLabel) (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)).paper_logKummer,
      (paperQPilotIdentificationsActual (l := fiveLabel) (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)).paper_qPilot_log⟩
  qPilotLogVolume_eq_multi :=
    paperQPilotObject_qPilotLogVolume_eq_multi (S2711O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) (S2711Donor R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)
  link_identification :=
    concreteSourceComparison (S2711O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) (S2711P R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D)
  link_implies_inclusion :=
    concreteMembership_of_sourceComparison (S2711O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)
      (S2711P R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D)

/-- The link identification of the multi-place source link is exactly the
concrete source comparison. -/
theorem S2711MultiSourceLink_identification
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {iota : Type} [Fintype iota] {W : iota -> Type}
    (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> W i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (nu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure nu]
    (D : SourcePilotRegionDonors (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)) :
    (S2711MultiSourceLink R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D).link_identification =
      concreteSourceComparison (S2711O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) (S2711P R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D) :=
  rfl

/-- The paper-level multi-place data: the corrected replacement of
PaperUnconditionalData.  It is inhabited from the actual data. -/
noncomputable def S2711PaperMultiUnconditionalData
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {iota : Type} [Fintype iota] {W : iota -> Type}
    (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> W i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (nu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure nu]
    (D : SourcePilotRegionDonors (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat))
    (v : FinitePrimePlace 2 7) :
    PaperUnconditionalDataMulti (l := fiveLabel) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel fiveLabel)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice fiveLabel)
      (I := S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)
      (G := ConcreteKummerGroup (l := fiveLabel))
      (envStrip := concreteQPilotStrip (l := fiveLabel))
      (X := PaperC6Carrier places tuple)
      (label := SignedLabel fiveLabel.value)
      v (S2711O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) (S2711Donor R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) (S2711P R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D) where
  sourceLink := S2711MultiSourceLink R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D
  sourceLink_holds := S2711_hcomp R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D
  thetaLink := concreteThetaLinkData (l := fiveLabel)

/-- The paper xi-f inequality for the concrete multi-place data. -/
theorem S2711_qPilot_le_signedHull
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {iota : Type} [Fintype iota] {W : iota -> Type}
    (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> W i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (nu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure nu]
    (D : SourcePilotRegionDonors (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)) :
    (S2711O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).qPilotLogVolume ≤
      (S2711P R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D).signedHullLogVolume :=
  S2711O_le_signedHull R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D

/-- The paper xi-f inequality in source-scalar form:
sourceQPilotSignedLog I.initial <= P.signedHullLogVolume. -/
theorem S2711_sourceQPilot_le_signedHull
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {iota : Type} [Fintype iota] {W : iota -> Type}
    (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> W i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (nu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure nu]
    (D : SourcePilotRegionDonors (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)) :
    sourceQPilotSignedLog (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).initial ≤
      (S2711P R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D).signedHullLogVolume := by
  calc sourceQPilotSignedLog (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).initial
      = (S2711O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).qPilotLogVolume :=
        (S2711O_qPilotLogVolume_eq_source R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).symm
    _ ≤ (S2711P R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D).signedHullLogVolume :=
        S2711_qPilot_le_signedHull R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D

/-! ## 8. The exact single-C3 obstruction -/

/-- Unfolded form of the single-completion equality forced by
PaperXiFSourceLink.qPilotLogVolume_eq_paper: the negative bad-q log sum equals
one completion log-norm. -/
theorem S2711_concreteSourceQ_iff_singleLog
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    (C3 : SourcePilotRegionData (l := fiveLabel) (V := FinitePrimePlace 2 7)
      (I := S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)) :
    ConcreteSourceQIdentification (I := S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) C3 ↔
      -sourceBadQAbsLog (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).initial = Real.log ‖C3.q.q‖ :=
  Iff.rfl

/-- Any paper-faithful single-C3 PaperUnconditionalData over the migrated
multi-place object forces the missing source-q identification.  This is the
exact object mismatch: the multi donor supplies the sum
-sourceBadQAbsLog I.initial, while the single-C3 field demands
localSignedLog C3.q. -/
theorem S2711_paperUnconditionalData_requires_sourceQ
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {iota : Type} [Fintype iota] {W : iota -> Type}
    (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> W i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (nu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure nu]
    (D : SourcePilotRegionDonors (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat))
    (v : FinitePrimePlace 2 7)
    (C3 : SourcePilotRegionData (l := fiveLabel) (V := FinitePrimePlace 2 7)
      (I := S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat))
    (M : PaperUnconditionalData (l := fiveLabel) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel fiveLabel)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice fiveLabel)
      (I := S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)
      (G := ConcreteKummerGroup (l := fiveLabel))
      (envStrip := concreteQPilotStrip (l := fiveLabel))
      (X := PaperC6Carrier places tuple)
      (label := SignedLabel fiveLabel.value)
      v (S2711O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) (S2711P R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D) C3) :
    ConcreteSourceQIdentification (I := S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) C3 := by
  have hqpaper : (S2711O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).qPilotLogVolume = paperQPilotLogVolume C3 :=
    (⟨M.sourceLink, M.sourceLink_holds⟩ :
      PaperXiFInclusion (S2711O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) (S2711P R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D)
        C3).qPilotLogVolume_eq_paper
  calc sourceQPilotSignedLog (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).initial
      = (S2711O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).qPilotLogVolume :=
        (S2711O_qPilotLogVolume_eq_source R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).symm
    _ = paperQPilotLogVolume C3 := hqpaper
    _ = localSignedLog C3.q := rfl

/-- Conversely, the missing source-q identification is exactly what suffices to
build the single-C3 PaperUnconditionalData over the migrated object.  Hence the
only gap is the scalar object identification, not the four paper identifications,
the comparison, or the Theta-link data. -/
noncomputable def S2711PaperUnconditionalData_of_sourceQ
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {iota : Type} [Fintype iota] {W : iota -> Type}
    (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> W i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (nu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure nu]
    (D : SourcePilotRegionDonors (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat))
    (v : FinitePrimePlace 2 7)
    (C3 : SourcePilotRegionData (l := fiveLabel) (V := FinitePrimePlace 2 7)
      (I := S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat))
    (hq : ConcreteSourceQIdentification (I := S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) C3) :
    PaperUnconditionalData (l := fiveLabel) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel fiveLabel)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice fiveLabel)
      (I := S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)
      (G := ConcreteKummerGroup (l := fiveLabel))
      (envStrip := concreteQPilotStrip (l := fiveLabel))
      (X := PaperC6Carrier places tuple)
      (label := SignedLabel fiveLabel.value)
      v (S2711O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) (S2711P R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D) C3 where
  sourceLink :=
    { source_identifications :=
        ⟨(paperQPilotIdentificationsActual (l := fiveLabel) (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)).paper_strip,
          (paperQPilotIdentificationsActual (l := fiveLabel) (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)).paper_lineBundle,
          (paperQPilotIdentificationsActual (l := fiveLabel) (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)).paper_logKummer,
          (paperQPilotIdentificationsActual (l := fiveLabel) (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)).paper_qPilot_log⟩
      qPilotLogVolume_eq_paper :=
        concreteO_qPilotLogVolume_eq_paper (S2711O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) C3 hq
      link_identification :=
        concreteSourceComparison (S2711O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) (S2711P R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D)
      link_implies_inclusion :=
        concreteMembership_of_sourceComparison (S2711O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)
          (S2711P R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D) }
  sourceLink_holds := S2711_hcomp R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D
  thetaLink := concreteThetaLinkData (l := fiveLabel)

/-! ## 9. Audit -/

#check S2711I
#check S2711Donor
#check S2711OBase
#check S2711O
#check S2711P
#check S2711P_average
#check S2711O_qPilotLogVolume_eq_base
#check S2711O_qPilotLogVolume_eq_source
#check S2711O_qPilotLogVolume
#check S2711_hcomp
#check S2711O_le_signedHull
#check S2711_hqMulti
#check S2711_hqMulti_eq
#check PaperUnconditionalDataMulti
#check PaperUnconditionalDataMulti.qPilot_le_signedHull
#check PaperUnconditionalDataMulti.hqMulti
#check S2711MultiSourceLink
#check S2711MultiSourceLink_identification
#check S2711PaperMultiUnconditionalData
#check S2711_qPilot_le_signedHull
#check S2711_sourceQPilot_le_signedHull
#check S2711_concreteSourceQ_iff_singleLog
#check S2711_paperUnconditionalData_requires_sourceQ
#check S2711PaperUnconditionalData_of_sourceQ

#print axioms S2711P_average
#print axioms S2711_hcomp
#print axioms S2711_hqMulti
#print axioms S2711O_qPilotLogVolume
#print axioms PaperUnconditionalDataMulti.qPilot_le_signedHull
#print axioms S2711MultiSourceLink
#print axioms S2711PaperMultiUnconditionalData
#print axioms S2711_qPilot_le_signedHull
#print axioms S2711_sourceQPilot_le_signedHull
#print axioms S2711_concreteSourceQ_iff_singleLog
#print axioms S2711_paperUnconditionalData_requires_sourceQ
#print axioms S2711PaperUnconditionalData_of_sourceQ

end LeanFormal.IUT.XiFPaper.S2711PaperMultiUnconditionalActual
end
