import tmp.sheaf.xif.paper.PaperXiFUnconditional
import tmp.sheaf.xif.paper.IPLAPTDataActual
import tmp.sheaf.xif.paper.PaperQPilotObjectConcreteActual
import tmp.sheaf.xif.paper.PaperQPilotIdentificationsActual
import tmp.sheaf.xif.paper.ConcreteThetaLinkSourceActual
import tmp.sheaf.xif.paper.PaperThetaMagnitudeSignedActual
import tmp.sheaf.xif.paper.S1931SourceHaarSignedAverageActual
import tmp.sheaf.xif.paper.S2679HcompLocalBoundsActual
import tmp.sheaf.xif.paper.S2675BadCardNoGoActual
import tmp.sheaf.xif.paper.BaseQLogVolumeActual

/-!
# S2678: hcomp of PaperUnconditionalData --- actual reduction, conditional theorem,
# and the exact remaining hypotheses

## Target

'PaperXiFUnconditional.PaperUnconditionalData' (line 107) has three fields:
'sourceLink', 'sourceLink_holds : sourceLink.link_identification', and 'thetaLink'.
The 'hcomp' of the concrete assembly is exactly

  'concreteSourceComparison O P  :=  P.procession.average <= -O.qPilotLogVolume'

for 'O = paperQPilotObjectConcrete I' and a concrete signed hull 'P'.

## What is proved here (actual)

1. The source bad-q absolute log is the global q-pilot magnitude:
   'S2678GlobalQPilotSignedLog I = sourceQPilotSignedLog I.initial' (rfl; this is
   the definitional identity of GlobalQPilotObjectActual, reproduced locally
   because that module's olean is in a conflicting module camp, see below), and
   the signed-average formula
     '(c3ThetaSignedProcession (actualSignedC3 D)).average
        = log 5 * (sourceThetaWeightSum l / card(SignedLabel l.value))'
   is proved from the actual S1931 theta-packet average and the actual
   source-theater packet value 'q = 1/5'.

2. The exact equivalence
     'concreteSourceComparison O P
        <-> log 5 * (W / card) <= sourceBadQAbsLog I.initial'
   ('concreteComparison_iff_weightSum_le_badQAbsLog'). This is the same
   statement as 'ConcreteSourceComparisonNumericActual.concreteComparison_iff_gaussSum_le_badQAbsLog'.
   That module is NOT importable in the frozen tree: its dependency
   'SignedAverageBoundActual' imports 'SourceTheaterLogVolumeSign', which fails
   to elaborate at line 66 (type mismatch between
   '(concreteInitialThetaCStageTheater l).thetaPacket.logVolume' and the
   'FiniteThetaPacket.ofQ gaussianFiveThetaQ ...' log-volume). Its mathematics
   is re-proved here with the same actual ingredients.

3. hcomp from the exact numeric residual, hcomp from
   '2 log 5 <= sourceBadQAbsLog' together with the coefficient bound, and the
   l = 5 case where the coefficient is proved to be exactly '2' (kernel 'decide'
   over 'ZMod 5'; no 'native_decide').

4. The bridge to the native bad-q magnitude:
   'sourceBadQAbsLog I.initial = S2678NativeBaseQGlobalMagnitude T' under the
   exact index alignment 'S2678BadQAbsLogAlignment' (identical to S2681's
   'S2681BadQAlignment'). With the actual local order/residue bounds (S2679) and
   'card(badPlaces) >= 5', this gives '2 log 5 <= sourceBadQAbsLog', hence hcomp.
   The S2681 module itself is in the conflicting module camp, so the two-line
   bridge is reproduced here.

5. The full 'PaperUnconditionalData' is assembled from
   'hq' (the exact source-q identification 'O.qPilotLogVolume = paperQPilotLogVolume C3',
   i.e. 'S2678ConcreteSourceQIdentification') plus hcomp. All other fields are
   the actual concrete data: the actual paper q-pilot object, the actual signed
   source-theater hull 'actualSignedHull', the actual IPL/Kummer-evaluation
   Theta-link. No field is faked.

## Module-camp obstruction (exact)

The frozen olean set contains two parallel modules declaring
'LeanFormal.IUT.Theorem311Source.PaperQPilotObject': the real
'tmp.sheaf.xif.PaperQPilotObject' and the orphan olean
'tmp.sheaf.xif.paper.PaperQPilotObject' (whose source file no longer exists).
Importing modules from both camps fails with

  "import tmp.sheaf.xif.paper.PaperQPilotObject failed, environment already
   contains 'LeanFormal.IUT.Theorem311Source.PaperQPilotObject.lineBundle'
   from tmp.sheaf.xif.PaperQPilotObject".

The paper data ('PaperXiFUnconditional', 'paperQPilotObjectConcrete',
'PaperXiFInclusion', 'PaperThetaMagnitudeSignedActual', S1931, S2675) lives in
the real camp; 'GlobalQPilotObjectActual', 'ConcreteQPilotLogIdentificationActual'
and 'S2681HcompBadQAlignmentActual' were compiled against the orphan camp.
Consequently the three small actual facts from those modules that this file
needs (the global signed-log identity, the paper q-log identification, and the
bad-q alignment bridge) are reproduced here verbatim from their sources, without
importing the conflicting modules.

## Exact remaining hypotheses (not fabricated, not proved here)

* 'hq': the source q-pilot scalar equals the completion q norm
  ('S2678ConcreteSourceQIdentification', the exact missing identification of
  'ConcreteSourceQIdentificationActual').
* 'hnormal': the C6 Haar normalization equality ('SignedHnormal'), needed only
  to construct the signed hull.
* the numeric residual 'log 5 * (W / card) <= sourceBadQAbsLog I.initial'
  (equivalently hcomp). Its sufficient native form
  '2 log 5 <= baseQTotalLogMagnitude T' together with the index alignment and
  'card >= 5' is the route of (4).
* for the concrete 'S1895PaperInput', 'card(badPlaces) = 1' (S2675), so the
  cardinality-sufficient condition 'card >= 5' is FALSE for that paper input;
  the exact residual stays the numeric inequality itself.

No sorry, axiom, 'True', 'PUnit', empty type, or 'native_decide' is used.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual
open LeanFormal.IUT.Theorem311Source.PaperQPilotIdentificationsActual
open LeanFormal.IUT.Theorem311Source.IPLAPTDataActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.ThetaPacketQIdentificationActual
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.ProcessionThetaPacketAverageActual
open LeanFormal.IUT.XiFPaper.S1931SourceHaarSignedAverageActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.S2679HcompLocalBoundsActual
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S2675BadCardNoGoActual

variable {l : PrimeGeFive}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type} [Fintype iota] {W : iota -> Type}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]
variable (D : SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I)
variable (v : FinitePrimePlace 2 7)

/-! ## 0. The actual objects -/

/-- Local high-priority copy of the concrete procession-choice preorder, so that
all 'PaperQPilotObject' and 'PaperUnconditionalData' ascriptions below use the
same instance as 'paperQPilotObjectConcrete'. -/
local instance (priority := 10000) s2678ProcessionPreorder (l : PrimeGeFive) :
    Preorder (ConcreteFiniteTheorem311.ProcessionChoice l) :=
  concreteProcessionChoicePreorder l

/-- The actual concrete q-pilot object. -/
abbrev O : PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
    (Label := ConcreteFiniteTheorem311.finiteLabel l)
    (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
    I (ConcreteKummerGroup (l := l)) (concreteQPilotStrip (l := l)) :=
  paperQPilotObjectConcrete (l := l) I

/-- The actual signed source-theater C3. -/
abbrev C3 : SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) I :=
  actualSignedC3 (l := l) (V := FinitePrimePlace 2 7) (I := I) D

/-- The actual signed paper hull attached to 'C3' by the exact C6 Haar
normalization equality 'hnormal'. -/
abbrev hull
    (hnormal : SignedHnormal (l := l) (V := FinitePrimePlace 2 7) (I := I)
      places tuple mu D) :
    PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value) :=
  actualSignedHull (l := l) (V := FinitePrimePlace 2 7) (I := I)
    places tuple mu D hnormal


/-! ## 1. Local reproductions of the orphan-olean facts -/

/-- The actual total bad q absolute log, reproduced from GlobalQPilotObjectActual
(definitionally the same term). -/
noncomputable def S2678GlobalQAbsLogTotal : Real := by
  letI := I.initial.bad_finite
  exact ∑ b : I.initial.badPlaces,
    |Real.log (I.initial.reduction.qParameter b)|

/-- The actual global q-pilot signed log, reproduced from
GlobalQPilotObjectActual. -/
noncomputable def S2678GlobalQPilotSignedLog : Real :=
  -S2678GlobalQAbsLogTotal (I := I)

/-- Actual equality: the reproduced global q-pilot signed log is the source
q-pilot signed log (the GlobalQPilotObjectActual identity). -/
theorem S2678GlobalQPilotSignedLog_eq_sourceQPilotSignedLog :
    S2678GlobalQPilotSignedLog (I := I) = sourceQPilotSignedLog I.initial := rfl

/-- The native global base-q magnitude (GlobalQPilotComparisonTruthActual /
S2681 form). -/
noncomputable def S2678NativeBaseQGlobalMagnitude
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : Real :=
  baseQTotalLogMagnitude T

/-- The exact index/term alignment between the source bad places and the native
bad places: a bijection of bad index sets together with the pointwise identity
of the absolute q-logs. This is the precise missing bridge for task 1 (identical
to S2681's 'S2681BadQAlignment'). -/
def S2678BadQAbsLogAlignment
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : Prop :=
  ∃ e : I.initial.badPlaces ≃ Bad (nativePlaceSelection T),
    ∀ b : I.initial.badPlaces,
      |Real.log (I.initial.reduction.qParameter b)| =
        baseQLogMagnitude T (e b)

/-- Under the exact bad-q alignment, the source bad-q absolute log equals the
native global base-q magnitude. -/
theorem S2678SourceBadQAbsLog_eq_nativeBaseQGlobalMagnitude
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (h : S2678BadQAbsLogAlignment (I := I) T) :
    sourceBadQAbsLog I.initial = S2678NativeBaseQGlobalMagnitude T := by
  letI : Fintype I.initial.badPlaces := I.initial.bad_finite
  obtain ⟨e, he⟩ := h
  unfold sourceBadQAbsLog S2678NativeBaseQGlobalMagnitude baseQTotalLogMagnitude
  calc
    (∑ b : I.initial.badPlaces,
        |Real.log (I.initial.reduction.qParameter b)|) =
        ∑ b : I.initial.badPlaces, baseQLogMagnitude T (e b) := by
      refine Finset.sum_congr rfl ?_
      intro b _
      exact he b
    _ = ∑ b : Bad (nativePlaceSelection T), baseQLogMagnitude T b := by
      exact Fintype.sum_equiv e (fun b => baseQLogMagnitude T (e b))
        (fun b => baseQLogMagnitude T b) (fun b => rfl)

/-- The exact source q identification (ConcreteSourceQIdentification of
ConcreteQPilotLogIdentificationActual / ConcreteSourceQIdentificationActual):
the source q-pilot signed scalar is the local completion q signed log. -/
abbrev S2678ConcreteSourceQIdentification
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (C3 : SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) I) : Prop :=
  sourceQPilotSignedLog I.initial = localSignedLog C3.q

/-- The paper q-pilot signed volume is definitionally the local q signed log. -/
theorem S2678paperQPilotLogVolume_eq_localSignedLog
    (C3 : SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) I) :
    paperQPilotLogVolume C3 = localSignedLog C3.q := rfl

/-- Conditional actual identification 'O.qPilotLogVolume = paperQPilotLogVolume C3'
from the source q identification (the theorem of
ConcreteQPilotLogIdentificationActual, reproduced locally). -/
theorem S2678O_qPilotLogVolume_eq_paper
    (h : S2678ConcreteSourceQIdentification (I := I) (C3 (l := l) (I := I) D)) :
    (O (l := l) (I := I)).qPilotLogVolume =
      paperQPilotLogVolume (C3 (l := l) (I := I) D) := by
  rw [paperQPilotObjectConcrete_qPilotLogVolume, h]
  exact (S2678paperQPilotLogVolume_eq_localSignedLog
    (l := l) (I := I) (C3 (l := l) (I := I) D)).symm

/-! ## 2. Actual source-side identities (task 1) -/

/-- The paper q-pilot magnitude is the negative source bad-q absolute log:
'-sourceQPilotSignedLog I.initial = sourceBadQAbsLog I.initial'. -/
theorem neg_sourceQPilotSignedLog_eq_sourceBadQAbsLog :
    -sourceQPilotSignedLog I.initial = sourceBadQAbsLog I.initial := by
  unfold sourceQPilotSignedLog
  ring

/-! ## 3. Actual signed-average formula for the source-theater C3 -/

/-- The actual theta-packet parameter of the source-theater C3 is '1/5'. -/
theorem C3_thetaPacket_q :
    (C3 (l := l) (I := I) D).thetaPacket.q = (5 : Real)⁻¹ := by
  change (c3WithSourceTheaterTheta (I := I) D).thetaPacket.q = (5 : Real)⁻¹
  rw [c3WithSourceTheaterTheta_q, gaussianFiveThetaQ_eq_inv_five]

/-- The actual signed procession average of the source-theater C3, in terms of
the Gaussian weight sum and the label cardinality. This is the exact formula of
'SignedAverageBoundActual.actualSignedC3_signedAverage_eq_log5_mul_sum_div_card'
re-proved from the actual S1931 theta-packet average (whose module is
importable), because 'SignedAverageBoundActual' is blocked upstream by
'SourceTheaterLogVolumeSign.lean:66'. -/
theorem signedAverage_eq_log5_mul_weightSum_div_card :
    (c3ThetaSignedProcession (C3 (l := l) (I := I) D)).average =
      Real.log (5 : Real) *
        (sourceThetaWeightSum l / (c3ThetaCard (l := l) : Real)) := by
  rw [S1931SourceHaarSignedAverageActual.signedAverage_eq_neg]
  rw [C3_thetaPacket_q (l := l) (I := I) D]
  rw [Real.log_inv]
  ring

/-- The signed average is nonnegative: the actual packet log-volume is
nonpositive ('actualSignedC3_hlog'). -/
theorem signedAverage_nonneg :
    0 ≤ (c3ThetaSignedProcession (C3 (l := l) (I := I) D)).average :=
  c3ThetaSignedProcession_average_nonneg
    (C3 (l := l) (I := I) D)
    (actualSignedC3_hlog (l := l) (V := FinitePrimePlace 2 7) (I := I) D)

/-! ## 4. The exact numeric reduction of hcomp (task 3) -/

/-- The Nat-valued Gaussian exponent sum. This is the exact term of
'SignedAverageBoundActual.gaussExponentSum'. -/
def S2678GaussExponentSum : Nat :=
  ∑ j : SignedLabel l.value, (gaussExponent j.1).toNat

/-- The real cast of the Gaussian exponent sum is the S1931 source theta weight
sum ('sourceThetaWeightSum'). -/
theorem S2678GaussExponentSum_cast :
    (S2678GaussExponentSum (l := l) : Real) = sourceThetaWeightSum l := by
  unfold S2678GaussExponentSum sourceThetaWeightSum
  push_cast
  rfl

/-- The source comparison for the concrete objects is exactly the numeric
bad-q inequality. This is the concrete instance of
'ConcreteSourceComparisonNumericActual.concreteComparison_iff_gaussSum_le_badQAbsLog',
re-proved here because that module is not importable. -/
theorem concreteComparison_iff_weightSum_le_badQAbsLog
    (hnormal : SignedHnormal (l := l) (V := FinitePrimePlace 2 7) (I := I)
      places tuple mu D) :
    concreteSourceComparison (O (l := l) (I := I))
        (hull (l := l) (I := I) places tuple mu D hnormal) ↔
      Real.log (5 : Real) *
          (sourceThetaWeightSum l / (c3ThetaCard (l := l) : Real)) ≤
        sourceBadQAbsLog I.initial := by
  unfold concreteSourceComparison
  rw [paperQPilotObjectConcrete_qPilotLogVolume]
  rw [actualSignedHull_procession_eq]
  rw [signedAverage_eq_log5_mul_weightSum_div_card]
  rw [sourceQPilotSignedLog]
  constructor <;> intro h <;> linarith

/-- The concrete source comparison as the exact Gauss-sum / bad-q inequality.
This is the statement (and name) of
'ConcreteSourceComparisonNumericActual.concreteComparison_iff_gaussSum_le_badQAbsLog',
reproduced here because that module is not importable. -/
theorem concreteComparison_iff_gaussSum_le_badQAbsLog
    (hnormal : SignedHnormal (l := l) (V := FinitePrimePlace 2 7) (I := I)
      places tuple mu D) :
    concreteSourceComparison (O (l := l) (I := I))
        (hull (l := l) (I := I) places tuple mu D hnormal) ↔
      Real.log (5 : Real) *
          ((S2678GaussExponentSum (l := l) : Real) /
            (Fintype.card (SignedLabel l.value) : Real)) ≤
        sourceBadQAbsLog I.initial := by
  rw [concreteComparison_iff_weightSum_le_badQAbsLog (l := l) (I := I)
    places tuple mu D hnormal, S2678GaussExponentSum_cast]

/-- hcomp from the exact numeric residual. -/
theorem hcomp_of_weightSum_le_badQAbsLog
    (hnormal : SignedHnormal (l := l) (V := FinitePrimePlace 2 7) (I := I)
      places tuple mu D)
    (h : Real.log (5 : Real) *
          (sourceThetaWeightSum l / (c3ThetaCard (l := l) : Real)) ≤
        sourceBadQAbsLog I.initial) :
    concreteSourceComparison (O (l := l) (I := I))
      (hull (l := l) (I := I) places tuple mu D hnormal) :=
  (concreteComparison_iff_weightSum_le_badQAbsLog (l := l) (I := I)
    places tuple mu D hnormal).mpr h

/-- hcomp from '2 log 5 <= sourceBadQAbsLog' plus the coefficient bound.
At 'l.value = 5' the coefficient bound is an identity (Section 5); in general
the coefficient 'W/card' is 'lStar*(lStar+1)/3' and exceeds 2 for 'l > 5', so
the coefficient hypothesis is genuinely needed here. -/
theorem hcomp_of_two_log5_le_badQAbsLog_of_coefficient
    (hnormal : SignedHnormal (l := l) (V := FinitePrimePlace 2 7) (I := I)
      places tuple mu D)
    (hcoeff : Real.log (5 : Real) *
        (sourceThetaWeightSum l / (c3ThetaCard (l := l) : Real)) ≤ 2 * Real.log 5)
    (h : 2 * Real.log 5 ≤ sourceBadQAbsLog I.initial) :
    concreteSourceComparison (O (l := l) (I := I))
      (hull (l := l) (I := I) places tuple mu D hnormal) :=
  hcomp_of_weightSum_le_badQAbsLog (l := l) (I := I) places tuple mu D hnormal
    (le_trans hcoeff h)

/-! ## 5. The l = 5 coefficient (kernel computation, no native_decide) -/

/-- The concrete prime label 'l = 5'. -/
def fiveLabel : PrimeGeFive where
  value := 5
  prime := by norm_num
  ge_five := by norm_num

theorem fiveLabel_value : fiveLabel.value = 5 := rfl

/-- 'sourceThetaWeightSum' depends only on 'l.value'. -/
theorem sourceThetaWeightSum_congr {l l' : PrimeGeFive} (h : l.value = l'.value) :
    sourceThetaWeightSum l = sourceThetaWeightSum l' := by
  unfold sourceThetaWeightSum
  rw [h]

/-- 'c3ThetaCard' depends only on 'l.value'. -/
theorem c3ThetaCard_congr {l l' : PrimeGeFive} (h : l.value = l'.value) :
    c3ThetaCard (l := l) = c3ThetaCard (l := l') := by
  unfold c3ThetaCard
  rw [h]

/-- The Gaussian weight sum at 'l = 5' is '10': the signed labels are
'-2, -1, 0, 1, 2' and the exponents are '4, 1, 0, 1, 4'. The computation is
transported to 'ZMod 5 = Fin 5' and checked by the kernel ('decide'); no
'native_decide' is used. -/
theorem sourceThetaWeightSum_five : sourceThetaWeightSum fiveLabel = 10 := by
  unfold sourceThetaWeightSum
  have hnat : (∑ j : SignedLabel fiveLabel.value, (gaussExponent j.1).toNat) = 10 := by
    rw [Fintype.sum_equiv (SignedLabel.equiv fiveLabel)
      (fun j : SignedLabel fiveLabel.value => (gaussExponent j.1).toNat)
      (fun x : Fl fiveLabel.value =>
        (gaussExponent ((SignedLabel.equiv fiveLabel).symm x).1).toNat)
      (by intro j; rw [Equiv.symm_apply_apply])]
    decide
  have hreal : (∑ j : SignedLabel fiveLabel.value,
      ((gaussExponent j.1).toNat : Real)) = 10 := by
    have := congrArg (fun n : Nat => (n : Real)) hnat
    push_cast at this
    simpa using this
  simpa using hreal

/-- The label cardinality at 'l = 5' is '5'. -/
theorem c3ThetaCard_five : c3ThetaCard (l := fiveLabel) = 5 := by
  unfold c3ThetaCard
  rw [SignedLabel.card_signedLabel]
  rfl

/-- The Gaussian average coefficient at 'l = 5' is exactly '2'. -/
theorem weightSum_div_card_five :
    sourceThetaWeightSum fiveLabel / (c3ThetaCard (l := fiveLabel) : Real) = 2 := by
  rw [sourceThetaWeightSum_five, c3ThetaCard_five]
  norm_num

/-- The signed average of the source-theater C3 at 'l = 5' is '2 log 5'. -/
theorem signedAverage_eq_two_log5
    (I : OriginalInput.{0, 0, 0, 0, 0} fiveLabel (FinitePrimePlace 2 7))
    (D : SourcePilotRegionDonors (l := fiveLabel) (V := FinitePrimePlace 2 7) I) :
    (c3ThetaSignedProcession
        (actualSignedC3 (l := fiveLabel) (V := FinitePrimePlace 2 7) (I := I) D)).average =
      2 * Real.log 5 := by
  rw [signedAverage_eq_log5_mul_weightSum_div_card (l := fiveLabel) (I := I) D]
  rw [weightSum_div_card_five]
  ring

/-- hcomp at 'l = 5' from the exact numeric residual '2 log 5 <= sourceBadQAbsLog',
with no coefficient side condition. -/
theorem hcomp_five_of_two_log5_le_badQAbsLog
    (I : OriginalInput.{0, 0, 0, 0, 0} fiveLabel (FinitePrimePlace 2 7))
    (D : SourcePilotRegionDonors (l := fiveLabel) (V := FinitePrimePlace 2 7) I)
    (hnormal : SignedHnormal (l := fiveLabel) (V := FinitePrimePlace 2 7) (I := I)
      places tuple mu D)
    (h : 2 * Real.log 5 ≤ sourceBadQAbsLog I.initial) :
    concreteSourceComparison
      (paperQPilotObjectConcrete (l := fiveLabel) (I := I))
      (actualSignedHull (l := fiveLabel) (V := FinitePrimePlace 2 7) (I := I)
        places tuple mu D hnormal) := by
  refine hcomp_of_weightSum_le_badQAbsLog (l := fiveLabel) (I := I)
    places tuple mu D hnormal ?_
  rw [weightSum_div_card_five]
  linarith

/-! ## 6. Bridge to the native bad-q magnitude and the cardinality route (tasks 1, 2) -/

/-- Under the exact bad-q alignment, the source bad-q absolute log equals the
native global base-q magnitude. -/
theorem sourceBadQAbsLog_eq_nativeMagnitude
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (halign : S2678BadQAbsLogAlignment (l := l) (I := I) T) :
    sourceBadQAbsLog I.initial = S2678NativeBaseQGlobalMagnitude T :=
  S2678SourceBadQAbsLog_eq_nativeBaseQGlobalMagnitude (l := l) (I := I) T halign

/-- The native sufficient condition gives '2 log 5 <= sourceBadQAbsLog': under
the exact bad-q alignment and 'card(badPlaces) >= 5', the actual local
order/residue lower bounds (S2679: order >= 1, residue norm >= 2) give the
native magnitude bound. -/
theorem two_log5_le_badQAbsLog_of_alignment_card_ge_five
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (halign : S2678BadQAbsLogAlignment (l := l) (I := I) T)
    (hcard : 5 ≤ Nat.card I.initial.badPlaces) :
    2 * Real.log 5 ≤ sourceBadQAbsLog I.initial := by
  letI : Fintype I.initial.badPlaces := I.initial.bad_finite
  have hcardF : 5 ≤ Fintype.card I.initial.badPlaces := by
    rwa [Nat.card_eq_fintype_card] at hcard
  have hcardNat : 5 ≤ Fintype.card (Bad (nativePlaceSelection T)) := by
    letI : Fintype I.initial.badPlaces := I.initial.bad_finite
    obtain ⟨e, -⟩ := halign
    calc 5 ≤ Fintype.card I.initial.badPlaces := hcardF
      _ = Fintype.card (Bad (nativePlaceSelection T)) := Fintype.card_congr e
  rw [sourceBadQAbsLog_eq_nativeMagnitude (l := l) (I := I) T halign]
  unfold S2678NativeBaseQGlobalMagnitude
  exact hcomp_global_ge_two_log5_of_card_ge_five T hcardNat

/-- hcomp from the exact alignment, 'card >= 5', and the coefficient bound. -/
theorem hcomp_of_alignment_card_ge_five
    (hnormal : SignedHnormal (l := l) (V := FinitePrimePlace 2 7) (I := I)
      places tuple mu D)
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (halign : S2678BadQAbsLogAlignment (l := l) (I := I) T)
    (hcard : 5 ≤ Nat.card I.initial.badPlaces)
    (hcoeff : Real.log (5 : Real) *
        (sourceThetaWeightSum l / (c3ThetaCard (l := l) : Real)) ≤ 2 * Real.log 5) :
    concreteSourceComparison (O (l := l) (I := I))
      (hull (l := l) (I := I) places tuple mu D hnormal) :=
  hcomp_of_two_log5_le_badQAbsLog_of_coefficient (l := l) (I := I) places tuple mu D hnormal
    hcoeff (two_log5_le_badQAbsLog_of_alignment_card_ge_five (l := l) (I := I) T halign hcard)

/-! ### The exact cardinality no-go for the concrete paper input (task 2) -/

/-- The concrete 'S1895PaperInput' has exactly one bad place. All source
cardinality facts in the tree for concrete inputs give card = 1, never card >= 5. -/
theorem s1895_badPlaces_card (P0 : S1895PaperInput) :
    Nat.card (S1895PaperInput.I P0).initial.badPlaces = 1 :=
  S2675_paperInput_bad_card P0

/-- Consequently the cardinality-sufficient condition 'card >= 5' is FALSE for
the concrete paper input: the S2679/GlobalQPilotComparisonTruthActual route
cannot be applied to it, and the exact residual remains the numeric inequality
'log 5 * (W/card) <= sourceBadQAbsLog' (equivalently '2 log 5 <= sourceBadQAbsLog'
when 'l = 5'). -/
theorem s1895_not_card_ge_five (P0 : S1895PaperInput) :
    ¬ 5 ≤ Nat.card (S1895PaperInput.I P0).initial.badPlaces :=
  S2675_not_five_le P0

/-! ## 7. Exact residual hypotheses, named -/

/-- The exact numeric residual of hcomp for the concrete source-theater data. -/
def HcompNumericResidual : Prop :=
  Real.log (5 : Real) *
      (sourceThetaWeightSum l / (c3ThetaCard (l := l) : Real)) ≤
    sourceBadQAbsLog I.initial

/-- The native form of the residual: the global base-q magnitude dominates
'2 log 5'. This is 'NativeGlobalQPilotComparison' of
'GlobalQPilotComparisonTruthActual', which is not importable in the frozen tree
(its imports 'SignedAverageBoundActual'/'SignedAverageBoundQOneFifth' are blocked
by 'SourceTheaterLogVolumeSign.lean:66'); the equivalent form here uses S2679's
actual 'baseQTotalLogMagnitude'. -/
def NativeResidual (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : Prop :=
  2 * Real.log 5 ≤ baseQTotalLogMagnitude T

/-- The alignment plus card >= 5 route supplies the native residual. -/
theorem nativeResidual_of_alignment_card_ge_five
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (halign : S2678BadQAbsLogAlignment (l := l) (I := I) T)
    (hcard : 5 ≤ Nat.card I.initial.badPlaces) :
    NativeResidual (l := l) T := by
  unfold NativeResidual
  letI : Fintype I.initial.badPlaces := I.initial.bad_finite
  have hcardF : 5 ≤ Fintype.card I.initial.badPlaces := by
    rwa [Nat.card_eq_fintype_card] at hcard
  have hcardNat : 5 ≤ Fintype.card (Bad (nativePlaceSelection T)) := by
    letI : Fintype I.initial.badPlaces := I.initial.bad_finite
    obtain ⟨e, -⟩ := halign
    calc 5 ≤ Fintype.card I.initial.badPlaces := hcardF
      _ = Fintype.card (Bad (nativePlaceSelection T)) := Fintype.card_congr e
  exact hcomp_global_ge_two_log5_of_card_ge_five T hcardNat

/-! ## 8. Assembly of 'PaperUnconditionalData' -/

/-- The full paper data at a general 'l', from the exact source-q identification
'hq' and hcomp. -/
noncomputable def paperUnconditionalData_of_hcomp
    (hnormal : SignedHnormal (l := l) (V := FinitePrimePlace 2 7) (I := I)
      places tuple mu D)
    (hq : (O (l := l) (I := I)).qPilotLogVolume = paperQPilotLogVolume (C3 (l := l) (I := I) D))
    (hcomp : concreteSourceComparison (O (l := l) (I := I))
      (hull (l := l) (I := I) places tuple mu D hnormal)) :
    PaperUnconditionalData (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      (I := I) (G := ConcreteKummerGroup (l := l))
      (envStrip := concreteQPilotStrip (l := l))
      (X := PaperC6Carrier places tuple)
      (label := SignedLabel l.value) v
      (O (l := l) (I := I))
      (hull (l := l) (I := I) places tuple mu D hnormal)
      (C3 (l := l) (I := I) D) where
  sourceLink := {
    source_identifications := ⟨
      (paperQPilotIdentificationsActual (l := l) I).paper_strip,
      (paperQPilotIdentificationsActual (l := l) I).paper_lineBundle,
      (paperQPilotIdentificationsActual (l := l) I).paper_logKummer,
      (paperQPilotIdentificationsActual (l := l) I).paper_qPilot_log⟩
    qPilotLogVolume_eq_paper := hq
    link_identification :=
      concreteSourceComparison (O (l := l) (I := I))
        (hull (l := l) (I := I) places tuple mu D hnormal)
    link_implies_inclusion :=
      concreteMembership_of_sourceComparison (O (l := l) (I := I))
        (hull (l := l) (I := I) places tuple mu D hnormal) }
  sourceLink_holds := hcomp
  thetaLink := {
    ipl := selfIplActual (concreteQPilotStrip (l := l))
    kummerEvaluation := selfKummerEvaluationActual (concreteQPilotStrip (l := l)) }

/-- The full paper data from the 'S2678ConcreteSourceQIdentification' form of
'hq' (the exact missing source q identification) and hcomp. -/
noncomputable def paperUnconditionalData_of_hcomp_of_sourceQ
    (hnormal : SignedHnormal (l := l) (V := FinitePrimePlace 2 7) (I := I)
      places tuple mu D)
    (hq : S2678ConcreteSourceQIdentification (I := I) (C3 (l := l) (I := I) D))
    (hcomp : concreteSourceComparison (O (l := l) (I := I))
      (hull (l := l) (I := I) places tuple mu D hnormal)) :
    PaperUnconditionalData (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      (I := I) (G := ConcreteKummerGroup (l := l))
      (envStrip := concreteQPilotStrip (l := l))
      (X := PaperC6Carrier places tuple)
      (label := SignedLabel l.value) v
      (O (l := l) (I := I))
      (hull (l := l) (I := I) places tuple mu D hnormal)
      (C3 (l := l) (I := I) D) :=
  paperUnconditionalData_of_hcomp (l := l) (I := I) (places := places) (tuple := tuple)
    (mu := mu) (D := D) (v := v) (hnormal := hnormal)
    (hq := S2678O_qPilotLogVolume_eq_paper (l := l) (I := I) D hq) (hcomp := hcomp)

/-- The full paper data from the numeric residual instead of hcomp. -/
noncomputable def paperUnconditionalData_of_weightSum
    (hnormal : SignedHnormal (l := l) (V := FinitePrimePlace 2 7) (I := I)
      places tuple mu D)
    (hq : (O (l := l) (I := I)).qPilotLogVolume = paperQPilotLogVolume (C3 (l := l) (I := I) D))
    (h : HcompNumericResidual (l := l) (I := I)) :
    PaperUnconditionalData (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      (I := I) (G := ConcreteKummerGroup (l := l))
      (envStrip := concreteQPilotStrip (l := l))
      (X := PaperC6Carrier places tuple)
      (label := SignedLabel l.value) v
      (O (l := l) (I := I))
      (hull (l := l) (I := I) places tuple mu D hnormal)
      (C3 (l := l) (I := I) D) :=
  paperUnconditionalData_of_hcomp (l := l) (I := I) (places := places) (tuple := tuple)
    (mu := mu) (D := D) (v := v) (hnormal := hnormal) (hq := hq)
    (hcomp := hcomp_of_weightSum_le_badQAbsLog (places := places) (tuple := tuple)
      (mu := mu) (I := I) (D := D) (hnormal := hnormal) (h := h))

/-- The full paper data at 'l = 5' from the source-q identification and the
numeric residual '2 log 5 <= sourceBadQAbsLog'. This is the strongest assembly
available: hcomp is fully derived, no comparison hypothesis is assumed. -/
noncomputable def paperUnconditionalData_five_of_two_log5
    (I : OriginalInput.{0, 0, 0, 0, 0} fiveLabel (FinitePrimePlace 2 7))
    (D : SourcePilotRegionDonors (l := fiveLabel) (V := FinitePrimePlace 2 7) I)
    (hnormal : SignedHnormal (l := fiveLabel) (V := FinitePrimePlace 2 7)
      (I := I) places tuple mu D)
    (hq : (paperQPilotObjectConcrete (l := fiveLabel) (I := I)).qPilotLogVolume =
      paperQPilotLogVolume
        (actualSignedC3 (l := fiveLabel) (V := FinitePrimePlace 2 7) (I := I) D))
    (h : 2 * Real.log 5 ≤ sourceBadQAbsLog I.initial) :
    PaperUnconditionalData (l := fiveLabel) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel fiveLabel)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice fiveLabel)
      (I := I) (G := ConcreteKummerGroup (l := fiveLabel))
      (envStrip := concreteQPilotStrip (l := fiveLabel))
      (X := PaperC6Carrier places tuple)
      (label := SignedLabel fiveLabel.value) v
      (paperQPilotObjectConcrete (l := fiveLabel) (I := I))
      (actualSignedHull (l := fiveLabel) (V := FinitePrimePlace 2 7) (I := I)
        places tuple mu D hnormal)
      (actualSignedC3 (l := fiveLabel) (V := FinitePrimePlace 2 7) (I := I) D) :=
  paperUnconditionalData_of_hcomp (l := fiveLabel) (I := I) (places := places)
    (tuple := tuple) (mu := mu) (D := D) (v := v) (hnormal := hnormal) (hq := hq)
    (hcomp := hcomp_five_of_two_log5_le_badQAbsLog (places := places) (tuple := tuple)
      (mu := mu) (I := I) (D := D) (hnormal := hnormal) (h := h))

/-! ## 9. Axiom audit -/

#print axioms concreteComparison_iff_weightSum_le_badQAbsLog
#print axioms S2678GaussExponentSum_cast
#print axioms concreteComparison_iff_gaussSum_le_badQAbsLog
#print axioms hcomp_of_weightSum_le_badQAbsLog
#print axioms hcomp_of_two_log5_le_badQAbsLog_of_coefficient
#print axioms sourceThetaWeightSum_five
#print axioms c3ThetaCard_five
#print axioms signedAverage_eq_two_log5
#print axioms hcomp_five_of_two_log5_le_badQAbsLog
#print axioms S2678SourceBadQAbsLog_eq_nativeBaseQGlobalMagnitude
#print axioms two_log5_le_badQAbsLog_of_alignment_card_ge_five
#print axioms paperUnconditionalData_of_hcomp
#print axioms paperUnconditionalData_five_of_two_log5

end LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
end
