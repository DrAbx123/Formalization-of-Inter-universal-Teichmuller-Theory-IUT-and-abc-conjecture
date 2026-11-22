import tmp.sheaf.xif.paper.ConcretePaperUnconditionalDataUnconditionalActual
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual

/-!
# S2686: concrete hq / hcomp for the unconditional PaperUnconditionalData

The unconditional target

  'LeanFormal.IUT.XiFPaper.ConcretePaperUnconditionalDataUnconditionalActual.concretePaperUnconditionalDataUnconditional'

takes exactly two scalar inputs:

* 'hq' : the qside q-log identification
    'ConcreteSourceQIdentification (I := I) (actualSignedC3 ... D)', i.e.
    'sourceQPilotSignedLog I.initial = localSignedLog (actualSignedC3 ... D).q';
* 'hcomp' : the concrete source comparison
    'concreteSourceComparison (concreteQPilotObject ...)
       (unconditionalHull ... places tuple nu D)', i.e.
    'average (unconditionalHull...) <= - (concreteQPilotObject...).qPilotLogVolume'.

This file fills both as far as the actual data permits, without faking anything:

1. 'hq' is characterised exactly as the source bad-q absolute log identity
   '-sourceBadQAbsLog I.initial = Real.log ‖(actualSignedC3 ... D).q.q‖'
   ('s2686HqResidual_iff_badQAbsLog'), and identified with the S2678 form of the
   source-q identification.

2. The unconditional hull carries the actual signed theta procession
   'c3ThetaSignedProcession (actualSignedC3 ... D)', hence its average is the
   actual Gaussian weight-sum value
   'Real.log 5 * (sourceThetaWeightSum l / c3ThetaCard l)'
   ('s2686UnconditionalHull_procession_eq', '..._average_eq').

3. 'hcomp' is proved equivalent to the exact numeric residual
   'HcompNumericResidual' ('s2686HcompResidual_iff_comparison'), and is derived
   from it ('s2686Hcomp_of_residual'). At 'l = 5' the residual reduces to
   '2 * Real.log 5 <= sourceBadQAbsLog I.initial'
   ('s2686Hcomp_five_of_two_log5').

4. The full unconditional paper data is assembled from 'hq' plus the numeric
   residual ('s2686PaperUnconditionalDataUnconditional_of_residual'), and at
   'l = 5' from 'hq' plus '2 log 5 <= sourceBadQAbsLog'
   ('..._five_of_two_log5').

5. The cardinality route is documented as a no-go for the concrete paper input:
   'Nat.card (S1895PaperInput.I P0).initial.badPlaces = 1', so
   '5 <= card' is false (S2678/S2675).

No sorry, axiom, True, PUnit, empty type or native_decide is used. The only
remaining inputs are 'hq' (the source q identification) and the numeric residual
'log 5 * (W/card) <= sourceBadQAbsLog' (equivalently '2 log 5 <= ...' at
'l = 5'); both are the actual remaining source comparisons, not faked.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2686PaperConcreteHqHcompActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual
open LeanFormal.IUT.Theorem311Source.ConcreteQPilotLogIdentificationActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.ConcretePaperUnconditionalDataActual
open LeanFormal.IUT.XiFPaper.ConcretePaperUnconditionalDataUnconditionalActual
open LeanFormal.IUT.XiFPaper.ConcreteSignedHullUnconditionalActual
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.S1931SourceHaarSignedAverageActual
open LeanFormal.IUT.XiFPaper.ProcessionThetaPacketAverageActual
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open MeasureTheory
open scoped BigOperators

universe ua upi umon ui

variable {l : PrimeGeFive}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type} [Fintype iota] {W : iota -> Type}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (nu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure nu]
variable (D : SourcePilotRegionDonors I)
variable (v : FinitePrimePlace 2 7)

/-- Local high-priority copy of the concrete procession-choice preorder, so that
all 'PaperQPilotObject' and 'PaperUnconditionalData' ascriptions below use the
same instance as 'paperQPilotObjectConcrete' (the same device as S2678). -/
local instance (priority := 10000) s2686ProcessionPreorder (l : PrimeGeFive) :
    Preorder (ConcreteFiniteTheorem311.ProcessionChoice l) :=
  concreteProcessionChoicePreorder l

/-! ## 1. hq: exact reduction of the source q identification -/

/-- The hq residual of the unconditional paper data: exactly the target's
qside q-log identification. -/
abbrev S2686HqResidual : Prop :=
  concreteQLogIdentification (l := l) (I := I) D

/-- The hcomp residual: exactly the numeric bad-q inequality of S2678. -/
abbrev S2686HcompResidual : Prop :=
  HcompNumericResidual (l := l) (I := I)

/-- hq is the paper q-pilot scalar equality
'sourceQPilotSignedLog = paperQPilotLogVolume (actualSignedC3 ... D)'. -/
theorem s2686HqResidual_iff_paperLog :
    S2686HqResidual (l := l) (I := I) D ↔
      sourceQPilotSignedLog I.initial =
        paperQPilotLogVolume
          (actualSignedC3 (l := l) (V := FinitePrimePlace 2 7) (I := I) D) :=
  Iff.rfl

/-- hq is the concrete scalar equality between the global source q-pilot log and
the completion q log norm. -/
theorem s2686HqResidual_iff_log_norm :
    S2686HqResidual (l := l) (I := I) D ↔
      sourceQPilotSignedLog I.initial =
        Real.log ‖(actualSignedC3 (l := l) (V := FinitePrimePlace 2 7)
          (I := I) D).q.q‖ := by
  rw [s2686HqResidual_iff_paperLog, paperQPilotLogVolume_eq_log_norm]

/-- Equivalently, the source bad-q absolute log equals the completion q
absolute log. -/
theorem s2686HqResidual_iff_badQAbsLog :
    S2686HqResidual (l := l) (I := I) D ↔
      -sourceBadQAbsLog I.initial =
        Real.log ‖(actualSignedC3 (l := l) (V := FinitePrimePlace 2 7)
          (I := I) D).q.q‖ := by
  rw [s2686HqResidual_iff_log_norm, sourceQPilotSignedLog]

/-- hq is exactly the S2678 source-q identification. -/
theorem s2686HqResidual_iff_S2678 :
    S2686HqResidual (l := l) (I := I) D ↔
      S2678ConcreteSourceQIdentification (I := I)
        (actualSignedC3 (l := l) (V := FinitePrimePlace 2 7) (I := I) D) :=
  Iff.rfl

/-! ## 2. The unconditional hull is the actual signed procession -/

/-- The unconditional hull (normalized Haar) carries the actual signed theta
procession. -/
theorem s2686UnconditionalHull_procession_eq :
    (unconditionalHull (l := l) places tuple nu D).procession =
      c3ThetaSignedProcession
        (actualSignedC3 (l := l) (V := FinitePrimePlace 2 7) (I := I) D) :=
  ConcreteSignedHullUnconditionalActual.unconditionalPaperSignedHull_procession_eq
    (l := l) (V := FinitePrimePlace 2 7) (I := I)
    (places := places) (tuple := tuple) (D := D) (nu := nu)

/-- The unconditional hull's signed average is the actual Gaussian weight-sum
value. -/
theorem s2686UnconditionalHull_average_eq :
    (unconditionalHull (l := l) places tuple nu D).procession.average =
      Real.log 5 *
        (sourceThetaWeightSum l / (c3ThetaCard (l := l) : Real)) := by
  rw [s2686UnconditionalHull_procession_eq]
  exact signedAverage_eq_log5_mul_weightSum_div_card (l := l) (I := I) (D := D)

/-! ## 3. hcomp: exact numeric residual -/

private theorem s2686_qPilotLogVolume_eq :
    (concreteQPilotObject (l := l) (I := I)).qPilotLogVolume =
      sourceQPilotSignedLog I.initial :=
  paperQPilotObjectConcrete_qPilotLogVolume I

/-- hcomp is exactly the numeric bad-q residual. -/
theorem s2686HcompResidual_iff_comparison :
    concreteSourceComparison (concreteQPilotObject (l := l) (I := I))
        (unconditionalHull (l := l) places tuple nu D) ↔
      S2686HcompResidual (l := l) (I := I) := by
  have havg := s2686UnconditionalHull_average_eq (l := l) (I := I)
    (places := places) (tuple := tuple) (nu := nu) (D := D)
  unfold concreteSourceComparison S2686HcompResidual HcompNumericResidual
  rw [s2686_qPilotLogVolume_eq (l := l) (I := I), havg, sourceQPilotSignedLog]
  constructor <;> intro h <;> linarith

/-- hcomp follows from the numeric residual. -/
theorem s2686Hcomp_of_residual
    (h : S2686HcompResidual (l := l) (I := I)) :
    concreteSourceComparison (concreteQPilotObject (l := l) (I := I))
      (unconditionalHull (l := l) places tuple nu D) :=
  (s2686HcompResidual_iff_comparison (l := l) (I := I)
    (places := places) (tuple := tuple) (nu := nu) (D := D)).mpr h

/-- hcomp from '2 log 5 <= sourceBadQAbsLog' plus the coefficient bound (the
coefficient bound is an identity at 'l = 5' and is needed for 'l > 5'). -/
theorem s2686Hcomp_of_two_log5_of_coefficient
    (hcoeff : Real.log 5 *
        (sourceThetaWeightSum l / (c3ThetaCard (l := l) : Real)) ≤
      2 * Real.log 5)
    (h : 2 * Real.log 5 ≤ sourceBadQAbsLog I.initial) :
    concreteSourceComparison (concreteQPilotObject (l := l) (I := I))
      (unconditionalHull (l := l) places tuple nu D) :=
  s2686Hcomp_of_residual (l := l) (I := I)
    (places := places) (tuple := tuple) (nu := nu) (D := D)
    (le_trans hcoeff h)

/-! ## 4. Assembly of the unconditional paper data -/

/-- The unconditional PaperUnconditionalData from hq and the exact numeric
residual. No further input is assumed. -/
noncomputable def s2686PaperUnconditionalDataUnconditional_of_residual
    (hq : S2686HqResidual (l := l) (I := I) D)
    (h : S2686HcompResidual (l := l) (I := I)) :
    PaperUnconditionalData (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      (I := I) (G := ConcreteKummerGroup (l := l))
      (envStrip := concreteQPilotStrip (l := l))
      (X := PaperC6Carrier places tuple)
      (label := SignedLabel l.value) v
      (concreteQPilotObject (l := l) (I := I))
      (unconditionalHull (l := l) places tuple nu D)
      (actualSignedC3 (l := l) (V := FinitePrimePlace 2 7) (I := I) D) :=
  concretePaperUnconditionalDataUnconditional (l := l) (I := I)
    (places := places) (tuple := tuple) (nu := nu) (D := D) (v := v)
    (hq := hq)
    (hcomp := s2686Hcomp_of_residual (l := l) (I := I)
      (places := places) (tuple := tuple) (nu := nu) (D := D) h)

/-- The unconditional PaperUnconditionalData from the S2678 source-q
identification and the numeric residual. -/
noncomputable def s2686PaperUnconditionalDataUnconditional_of_sourceQ_residual
    (hq : S2678ConcreteSourceQIdentification (I := I)
      (actualSignedC3 (l := l) (V := FinitePrimePlace 2 7) (I := I) D))
    (h : S2686HcompResidual (l := l) (I := I)) :
    PaperUnconditionalData (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      (I := I) (G := ConcreteKummerGroup (l := l))
      (envStrip := concreteQPilotStrip (l := l))
      (X := PaperC6Carrier places tuple)
      (label := SignedLabel l.value) v
      (concreteQPilotObject (l := l) (I := I))
      (unconditionalHull (l := l) places tuple nu D)
      (actualSignedC3 (l := l) (V := FinitePrimePlace 2 7) (I := I) D) :=
  s2686PaperUnconditionalDataUnconditional_of_residual (l := l) (I := I)
    (places := places) (tuple := tuple) (nu := nu) (D := D) (v := v)
    ((s2686HqResidual_iff_S2678 (l := l) (I := I) (D := D)).mpr hq) h

/-! ## 5. The 'l = 5' case: the coefficient is exactly '2' -/

/-- At 'l = 5' the unconditional hull's signed average is exactly '2 log 5'. -/
theorem s2686UnconditionalHull_average_five
    {I5 : OriginalInput.{0, 0, 0, 0, 0} fiveLabel (FinitePrimePlace 2 7)}
    (D5 : SourcePilotRegionDonors I5) :
    (unconditionalHull (l := fiveLabel) places tuple nu D5).procession.average =
      2 * Real.log 5 := by
  rw [s2686UnconditionalHull_procession_eq (l := fiveLabel) (I := I5)
    (places := places) (tuple := tuple) (nu := nu) (D := D5)]
  exact signedAverage_eq_two_log5 I5 D5

/-- hcomp at 'l = 5' from the exact numeric residual
'2 log 5 <= sourceBadQAbsLog'. -/
theorem s2686Hcomp_five_of_two_log5
    {I5 : OriginalInput.{0, 0, 0, 0, 0} fiveLabel (FinitePrimePlace 2 7)}
    (D5 : SourcePilotRegionDonors I5)
    (h : 2 * Real.log 5 ≤ sourceBadQAbsLog I5.initial) :
    concreteSourceComparison (concreteQPilotObject (l := fiveLabel) (I := I5))
      (unconditionalHull (l := fiveLabel) places tuple nu D5) := by
  have hqvol : (concreteQPilotObject (l := fiveLabel) (I := I5)).qPilotLogVolume =
      sourceQPilotSignedLog I5.initial :=
    paperQPilotObjectConcrete_qPilotLogVolume I5
  have havg := s2686UnconditionalHull_average_five
    (places := places) (tuple := tuple) (nu := nu) (I5 := I5) (D5 := D5)
  unfold concreteSourceComparison
  rw [hqvol, havg, sourceQPilotSignedLog]
  linarith

/-- The unconditional PaperUnconditionalData at 'l = 5' from hq and
'2 log 5 <= sourceBadQAbsLog'. This is the strongest unconditional assembly
available: hcomp is fully derived, and hq is the only scalar identification. -/
noncomputable def s2686PaperUnconditionalDataUnconditional_five_of_two_log5
    {I5 : OriginalInput.{0, 0, 0, 0, 0} fiveLabel (FinitePrimePlace 2 7)}
    (D5 : SourcePilotRegionDonors I5)
    (hq : concreteQLogIdentification (l := fiveLabel) (I := I5) D5)
    (h : 2 * Real.log 5 ≤ sourceBadQAbsLog I5.initial) :
    PaperUnconditionalData (l := fiveLabel) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel fiveLabel)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice fiveLabel)
      (I := I5) (G := ConcreteKummerGroup (l := fiveLabel))
      (envStrip := concreteQPilotStrip (l := fiveLabel))
      (X := PaperC6Carrier places tuple)
      (label := SignedLabel fiveLabel.value) v
      (concreteQPilotObject (l := fiveLabel) (I := I5))
      (unconditionalHull (l := fiveLabel) places tuple nu D5)
      (actualSignedC3 (l := fiveLabel) (V := FinitePrimePlace 2 7) (I := I5) D5) :=
  concretePaperUnconditionalDataUnconditional (l := fiveLabel) (I := I5)
    (places := places) (tuple := tuple) (nu := nu) (D := D5) (v := v)
    (hq := hq)
    (hcomp := s2686Hcomp_five_of_two_log5
      (places := places) (tuple := tuple) (nu := nu) (I5 := I5) (D5 := D5) h)

/-! ## 6. The exact residual and the cardinality no-go -/

/-- The exact residual pair of the unconditional paper data. -/
structure S2686ResidualPair : Prop where
  /-- The source q identification (hq). -/
  hq : S2686HqResidual (l := l) (I := I) D
  /-- The numeric bad-q residual (hcomp). -/
  hcomp : S2686HcompResidual (l := l) (I := I)

/-- The residual pair is exactly the pair of target inputs. -/
theorem s2686ResidualPair_iff :
    S2686ResidualPair (l := l) (I := I) D ↔
      (concreteQLogIdentification (l := l) (I := I) D ∧
        HcompNumericResidual (l := l) (I := I)) := by
  constructor
  · intro hp
    exact ⟨hp.hq, hp.hcomp⟩
  · intro hp
    exact ⟨hp.1, hp.2⟩

/-- The concrete 'S1895PaperInput' has exactly one bad place, so the
cardinality-sufficient condition 'card >= 5' used by the S2679 native route is
FALSE for the concrete paper input. -/
theorem s2686_s1895_badPlaces_card (P0 : S1895PaperInput) :
    Nat.card (S1895PaperInput.I P0).initial.badPlaces = 1 :=
  s1895_badPlaces_card P0

/-- Consequently the cardinality route cannot be applied to the concrete paper
input; the exact numeric residual stays the required input. -/
theorem s2686_s1895_not_card_ge_five (P0 : S1895PaperInput) :
    ¬ 5 ≤ Nat.card (S1895PaperInput.I P0).initial.badPlaces :=
  s1895_not_card_ge_five P0

/-! ## 7. Axiom audit -/

#print axioms s2686HqResidual_iff_badQAbsLog
#print axioms s2686UnconditionalHull_procession_eq
#print axioms s2686HcompResidual_iff_comparison
#print axioms s2686PaperUnconditionalDataUnconditional_of_residual
#print axioms s2686PaperUnconditionalDataUnconditional_five_of_two_log5
#print axioms s2686_s1895_badPlaces_card

end LeanFormal.IUT.XiFPaper.S2686PaperConcreteHqHcompActual

end
