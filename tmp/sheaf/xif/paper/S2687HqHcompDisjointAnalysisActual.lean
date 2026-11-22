/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual
import tmp.sheaf.xif.paper.S2681HcompMinimalInputActual
import tmp.sheaf.xif.paper.S2680TateQIdentificationAssemblyActual
import tmp.sheaf.xif.paper.S2682CurveIndexedTateSplitActual

/-!
# S2687: the disjoint hq / hcomp residual interface for the paper route

Consumer: `PaperXiFUnconditional.PaperUnconditionalData` (via the actual
S2678 assembly) and the hcomp chain of S2681.

## Target

`PaperUnconditionalData` (PaperXiFUnconditional.lean:107) has three fields,
`sourceLink`, `sourceLink_holds` and `thetaLink`.  On the concrete paper
route (S2678) the only two non-structural fields are

* `sourceLink.qPilotLogVolume_eq_paper : O.qPilotLogVolume = paperQPilotLogVolume C3`,
  which is exactly the source q identification
  `S2678ConcreteSourceQIdentification I C3` (`sourceQPilotSignedLog I.initial =
  localSignedLog C3.q`), and
* `sourceLink_holds : concreteSourceComparison O P`
  (`P.procession.average <= -O.qPilotLogVolume`), which S2678 proves
  equivalent to the numeric residual `HcompNumericResidual I`
  (`log 5 * (W / card) <= sourceBadQAbsLog I.initial`).

The hcomp chain (S2681) measures the same comparison by the *native* bad-q
magnitude `2 log 5 <= baseQTotalLogMagnitude T` (`HcompBadQData T`) and
proves that, under the index alignment `S2678BadQAbsLogAlignment I T`, at
`l = 5` the comparison is exactly that single numeric inequality
(`S2681HcompMinimalInputActual.hcomp_iff_badQData_five`).

## What this file proves

1. `HqHcompResidual I T D` is the single interface bundling exactly those two
   residuals, with the *existing* names (`S2678ConcreteSourceQIdentification`
   and `HcompNumericResidual`).  No duplicate residual is introduced.

2. `paperUnconditionalData_of_hqHcompResidual` assembles the full
   `PaperUnconditionalData` from the interface.  The `hcomp` comparison is
   *derived* from the numeric residual
   (`S2678...concreteComparison_iff_weightSum_le_badQAbsLog`); it is never
   assumed as a comparison under another name.  `hq` is used only for the
   `qPilotLogVolume_eq_paper` field.

3. `hq` is separated from `hcomp`: `hq` is equivalent to the T-free scalar
   identity `sourceBadQAbsLog I.initial = |log (paperQParameter C3)|`
   (`sourceQIdentification_iff_abs_paperQParameter`), while `hcomp` is the
   numeric inequality.  At `l = 5` the hcomp part is proved equivalent to
   `2 log 5 <= sourceBadQAbsLog I.initial` and, under the alignment, to
   `HcompBadQData T` (`numericResidual_iff_hcompBadQData_five`, the S2681
   equivalence transported to the actual signed hull).

4. The pair is *not* jointly reducible to a single inequality: the identity
   determines `sourceBadQAbsLog` from `paperQParameter C3`, and an
   inequality cannot do that (`identity_not_absorbed_by_bound`).  The exact
   residual list is therefore `{hq (equality), hcomp (one numeric inequality at
   l = 5)}`.

5. The third (disjoint) residual, the analytic Tate input, is located through
   the actual S2682 coordinate/analytic split and the actual S2680 conditional
   D4 Tate-q identification.  Its statements contain no `C3` and no q-pilot
   scalar, so it is independent of both `hq` and the numeric residual; and
   hcomp does not consume it (S2681 `hcomp_of_agreement_badQ`).

## Honest scope

No residual is asserted, no inhabitant of `HqHcompResidual` is constructed, no
`PaperUnconditionalData` is produced unconditionally.  No `sorry`,
`axiom`, `True`, `PUnit`, empty type or `native_decide` is used.  No
volumedet-owned file is imported or modified.

## Module notes

All four imported ACTUAL modules have oleans in the frozen build set
(`S2678PaperUnconditionalHcompActual`, `S2681HcompMinimalInputActual`,
`S2680TateQIdentificationAssemblyActual`,
`S2682CurveIndexedTateSplitActual`).  This file stays on the real module camp
(`tmp.sheaf.xif.PaperQPilotObject`, not the orphan
`tmp.sheaf.xif.paper.PaperQPilotObject` olean); the S2678 local reproductions
are used for every orphan-camp fact (source q identification, weight-sum/average
formula).
-/

noncomputable section
open scoped BigOperators
open MeasureTheory
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2687HqHcompDisjointAnalysisActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.InitialThetaSource.PlaceQParameterUniformization
open LeanFormal.IUT.InitialThetaSource.PlaceTateComparisonConstruction
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.ProcessionThetaPacketAverageActual
open LeanFormal.IUT.XiFPaper.S1931SourceHaarSignedAverageActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.S2679HcompLocalBoundsActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.XiFPaper.S436KSideQVActual
open LeanFormal.IUT.XiFPaper.S1444ReportAKPlaceQActual
open LeanFormal.IUT.XiFPaper.S1493KSideTateTransportActual

variable {l : PrimeGeFive}
variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type} [Fintype iota] {W : iota -> Type}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]
variable {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
variable {T : SourceNativeInitialThetaData.{0} l}
variable (D : SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I)
variable (v : FinitePrimePlace 2 7)

/-- Local high-priority copy of the concrete procession-choice preorder, so that
the `PaperQPilotObject`/`PaperUnconditionalData` ascriptions below use the
same instance as `paperQPilotObjectConcrete` (the device used in S2678). -/
local instance (priority := 10000) s2687ProcessionPreorder (l : PrimeGeFive) :
    Preorder (ConcreteFiniteTheorem311.ProcessionChoice l) :=
  concreteProcessionChoicePreorder l

/-! ## 1. The single interface: hq + the hcomp numeric residual -/

/-- The two non-structural residuals of the paper route.

* `hq` is the source q identification `S2678ConcreteSourceQIdentification I C3`,
  i.e. `sourceQPilotSignedLog I.initial = localSignedLog C3.q`.  It is exactly
  the field `sourceLink.qPilotLogVolume_eq_paper` of `PaperUnconditionalData`.
* `hcomp` is the numeric bad-q residual `HcompNumericResidual I`, i.e.
  `log 5 * (W / card) <= sourceBadQAbsLog I.initial`.  It is exactly the
  numeric form of `concreteSourceComparison O P` (S2678), hence of
  `sourceLink_holds`; at `l = 5` it is literally
  `2 log 5 <= sourceBadQAbsLog I.initial` (S2681 `HcompSourceBadQData`).

`T` is the native source datum.  The two residuals themselves are stated on
the source side (they do not mention `T`); `T` enters only through the
equivalent native form `HcompBadQData T`
(`2 log 5 <= baseQTotalLogMagnitude T`), which is equivalent to `hcomp`
under the index alignment `S2678BadQAbsLogAlignment I T` (Section 3).  No new
residual is introduced: both components are the existing S2678/S2681
declarations. -/
structure HqHcompResidual
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (T : SourceNativeInitialThetaData.{0} l)
    (D : SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I) where
  /-- hq: the source q-pilot scalar identification. -/
  hq : S2678ConcreteSourceQIdentification (I := I) (C3 (l := l) (I := I) (D := D))
  /-- hcomp: the numeric bad-q residual. -/
  hcomp : HcompNumericResidual (l := l) (I := I)

/-- `hq` in the exact form consumed by `PaperUnconditionalData`: the object
scalar is the actual paper q-pilot scalar of `C3`. -/
theorem hq_eq_paperQPilotLogVolume
    (R : HqHcompResidual (l := l) (I := I) (T := T) (D := D)) :
    (O (l := l) (I := I)).qPilotLogVolume =
      paperQPilotLogVolume (C3 (l := l) (I := I) (D := D)) :=
  S2678O_qPilotLogVolume_eq_paper (l := l) (I := I) (D := D) (h := R.hq)

/-! ## 2. Separating hq: it is a T-free scalar identity

`hq` is an identification of two real scalars, not a bound.  Concretely it
says that the source bad-q absolute log equals the absolute log of the paper q
parameter of `C3`.  This is the disjoint, equality-shaped half of the pair. -/

/-- The source q identification is exactly the scalar identity
`sourceBadQAbsLog I.initial = |log (paperQParameter C3)|`.

Proof: `sourceQPilotSignedLog = -sourceBadQAbsLog`,
`paperQPilotLogVolume C3 = localSignedLog C3.q` and
`paperQPilotLogVolume C3 = -|log (paperQParameter C3)|`. -/
theorem sourceQIdentification_iff_abs_paperQParameter :
    S2678ConcreteSourceQIdentification (I := I) (C3 (l := l) (I := I) (D := D)) ↔
      sourceBadQAbsLog I.initial =
        |Real.log (paperQParameter (C3 (l := l) (I := I) (D := D)))| := by
  have hsource : -sourceQPilotSignedLog I.initial = sourceBadQAbsLog I.initial :=
    neg_sourceQPilotSignedLog_eq_sourceBadQAbsLog (I := I)
  have hpaper : paperQPilotLogVolume (C3 (l := l) (I := I) (D := D)) =
      -|Real.log (paperQParameter (C3 (l := l) (I := I) (D := D)))| :=
    paperQPilotLogVolume_eq_neg_abs_paperQParameter
      (C3 (l := l) (I := I) (D := D))
  have hloc : paperQPilotLogVolume (C3 (l := l) (I := I) (D := D)) =
      localSignedLog (C3 (l := l) (I := I) (D := D)).q := rfl
  unfold S2678ConcreteSourceQIdentification
  constructor
  · intro h
    calc sourceBadQAbsLog I.initial
        = -sourceQPilotSignedLog I.initial := hsource.symm
      _ = -localSignedLog (C3 (l := l) (I := I) (D := D)).q := by rw [h]
      _ = -paperQPilotLogVolume (C3 (l := l) (I := I) (D := D)) := by rw [hloc]
      _ = |Real.log (paperQParameter (C3 (l := l) (I := I) (D := D)))| := by
            rw [hpaper]; ring
  · intro h
    have h2 : sourceQPilotSignedLog I.initial =
        -|Real.log (paperQParameter (C3 (l := l) (I := I) (D := D)))| := by
      linarith [hsource, h]
    calc sourceQPilotSignedLog I.initial
        = -|Real.log (paperQParameter (C3 (l := l) (I := I) (D := D)))| := h2
      _ = paperQPilotLogVolume (C3 (l := l) (I := I) (D := D)) := hpaper.symm
      _ = localSignedLog (C3 (l := l) (I := I) (D := D)).q := hloc

/-! ## 3. The hcomp half: one numeric inequality -/

/-- The numeric residual is exactly the concrete source comparison (S2678).
This derivation mentions neither `C3` nor `hq`: the hcomp half is
independent of the source q identification. -/
theorem concreteSourceComparison_of_numericResidual
    (hnormal : SignedHnormal (l := l) (V := FinitePrimePlace 2 7) (I := I)
      places tuple mu D)
    (h : HcompNumericResidual (l := l) (I := I)) :
    concreteSourceComparison (O (l := l) (I := I))
      (hull (l := l) (I := I) places tuple mu D hnormal) :=
  hcomp_of_weightSum_le_badQAbsLog (l := l) (I := I) (places := places)
    (tuple := tuple) (mu := mu) (D := D) (hnormal := hnormal) (h := h)

/-- The same derivation from the full interface: only the `hcomp` field is
consumed. -/
theorem concreteSourceComparison_of_hqHcompResidual
    (hnormal : SignedHnormal (l := l) (V := FinitePrimePlace 2 7) (I := I)
      places tuple mu D)
    (R : HqHcompResidual (l := l) (I := I) (T := T) (D := D)) :
    concreteSourceComparison (O (l := l) (I := I))
      (hull (l := l) (I := I) places tuple mu D hnormal) :=
  concreteSourceComparison_of_numericResidual (l := l) (I := I)
    (places := places) (tuple := tuple) (mu := mu) (D := D) (hnormal := hnormal)
    R.hcomp

/-- At `l = 5` the numeric residual is literally
`2 log 5 <= sourceBadQAbsLog I.initial` (the Gaussian coefficient is exactly
2). -/
theorem numericResidual_iff_two_log5_five (hl : l.value = 5) :
    HcompNumericResidual (l := l) (I := I) ↔
      2 * Real.log 5 ≤ sourceBadQAbsLog I.initial := by
  unfold HcompNumericResidual
  rw [S2681HcompMinimalInputActual.weightSum_div_card_eq_two_of_value_eq_five
    (l := l) hl]
  constructor <;> intro h <;> linarith

/-- The comparison at `l = 5` from the literal numeric residual
`2 log 5 <= sourceBadQAbsLog`, with no coefficient side condition. -/
theorem concreteSourceComparison_five_of_two_log5
    (hnormal : SignedHnormal (l := l) (V := FinitePrimePlace 2 7) (I := I)
      places tuple mu D)
    (hl : l.value = 5)
    (h : 2 * Real.log 5 ≤ sourceBadQAbsLog I.initial) :
    concreteSourceComparison (O (l := l) (I := I))
      (hull (l := l) (I := I) places tuple mu D hnormal) :=
  concreteSourceComparison_of_numericResidual (l := l) (I := I)
    (places := places) (tuple := tuple) (mu := mu) (D := D) (hnormal := hnormal)
    ((numericResidual_iff_two_log5_five (l := l) (I := I) hl).mpr h)

/-- S2681's `hcomp_iff_badQData_five`, transported to the actual signed hull:
at `l = 5`, given the index alignment, the concrete source comparison is
*exactly* the single numeric inequality `2 log 5 <= baseQTotalLogMagnitude T`. -/
theorem hcompBadQData_iff_comparison_five
    (hnormal : SignedHnormal (l := l) (V := FinitePrimePlace 2 7) (I := I)
      places tuple mu D)
    [Fintype (Bad (nativePlaceSelection T))]
    (hl : l.value = 5)
    (halign : S2678BadQAbsLogAlignment (l := l) (I := I) T) :
    S2681HcompMinimalInputActual.HcompBadQData T ↔
      concreteSourceComparison (O (l := l) (I := I))
        (hull (l := l) (I := I) places tuple mu D hnormal) :=
  (S2681HcompMinimalInputActual.hcomp_iff_badQData_five (l := l) (I := I) (D := D)
    (hull (l := l) (I := I) places tuple mu D hnormal) T
    (hP := congrArg (fun pr => pr.average)
      (actualSignedHull_procession_eq (l := l) (V := FinitePrimePlace 2 7)
        (I := I) places tuple mu D hnormal))
    (hl := hl) (halign := halign)).symm

/-- At `l = 5` (given the index alignment) the exact numeric residual and the
native residual `HcompBadQData T` are the same single inequality. -/
theorem numericResidual_iff_hcompBadQData_five
    [Fintype (Bad (nativePlaceSelection T))]
    (halign : S2678BadQAbsLogAlignment (l := l) (I := I) T)
    (hl : l.value = 5) :
    HcompNumericResidual (l := l) (I := I) ↔
      S2681HcompMinimalInputActual.HcompBadQData T := by
  rw [numericResidual_iff_two_log5_five (l := l) (I := I) hl]
  constructor
  · intro h
    unfold S2681HcompMinimalInputActual.HcompBadQData
    rwa [S2681HcompMinimalInputActual.sourceBadQAbsLog_eq_baseQTotalLogMagnitude
      (l := l) (I := I) T halign] at h
  · intro h
    exact S2681HcompMinimalInputActual.two_log5_le_sourceBadQAbsLog
      (l := l) (I := I) T halign h

/-- Native constructor at `l = 5`: the source q identification plus the native
bad-q data (and the index alignment) give the interface. -/
theorem hqHcompResidual_of_native_five
    [Fintype (Bad (nativePlaceSelection T))]
    (hq : S2678ConcreteSourceQIdentification (I := I) (C3 (l := l) (I := I) (D := D)))
    (hl : l.value = 5)
    (halign : S2678BadQAbsLogAlignment (l := l) (I := I) T)
    (hbad : S2681HcompMinimalInputActual.HcompBadQData T) :
    HqHcompResidual (l := l) (I := I) (T := T) (D := D) :=
  ⟨hq, (numericResidual_iff_hcompBadQData_five (l := l) (I := I) (T := T)
    (halign := halign) (hl := hl)).mpr hbad⟩

/-- Converse at `l = 5`: the interface gives the native bad-q data. -/
theorem hcompBadQData_of_hqHcompResidual_five
    (R : HqHcompResidual (l := l) (I := I) (T := T) (D := D))
    [Fintype (Bad (nativePlaceSelection T))]
    (hl : l.value = 5)
    (halign : S2678BadQAbsLogAlignment (l := l) (I := I) T) :
    S2681HcompMinimalInputActual.HcompBadQData T :=
  (numericResidual_iff_hcompBadQData_five (l := l) (I := I) (T := T)
    (halign := halign) (hl := hl)).mp R.hcomp

/-! ## 4. The residual pair on the paper q side

`hq` identifies `sourceBadQAbsLog` with `|log (paperQParameter C3)|`; the
numeric residual is then the same inequality on that value.  The pair is
therefore `(identity) ∧ (one inequality)`, and the identity cannot be
absorbed into the inequality. -/

/-- The two residuals read on the paper q side. -/
theorem paperQParameter_of_hqHcompResidual
    (R : HqHcompResidual (l := l) (I := I) (T := T) (D := D)) :
    sourceBadQAbsLog I.initial =
        |Real.log (paperQParameter (C3 (l := l) (I := I) (D := D)))| ∧
      Real.log 5 * (sourceThetaWeightSum l / (c3ThetaCard (l := l) : Real)) ≤
        |Real.log (paperQParameter (C3 (l := l) (I := I) (D := D)))| := by
  have hq := (sourceQIdentification_iff_abs_paperQParameter (l := l) (I := I)
    (D := D)).mp R.hq
  refine ⟨hq, ?_⟩
  rw [← hq]
  exact R.hcomp

/-- The converse reading: the scalar identity plus the inequality on the paper
q parameter give the interface. -/
theorem hqHcompResidual_of_paperQParameter
    (hq : sourceBadQAbsLog I.initial =
      |Real.log (paperQParameter (C3 (l := l) (I := I) (D := D)))|)
    (hcomp : Real.log 5 * (sourceThetaWeightSum l / (c3ThetaCard (l := l) : Real)) ≤
      |Real.log (paperQParameter (C3 (l := l) (I := I) (D := D)))|) :
    HqHcompResidual (l := l) (I := I) (T := T) (D := D) := by
  refine ⟨(sourceQIdentification_iff_abs_paperQParameter (l := l) (I := I)
    (D := D)).mpr hq, ?_⟩
  show Real.log 5 * (sourceThetaWeightSum l / (c3ThetaCard (l := l) : Real)) ≤
    sourceBadQAbsLog I.initial
  rw [hq]
  exact hcomp

/-- The residual pair is strictly stronger than the numeric inequality alone:
an identity `a = b` is not implied by a lower bound on `b`, so `hq` cannot
be absorbed into the numeric residual.  This is the precise sense in which the
two residuals are disjoint (and why the pair is not one inequality). -/
theorem identity_not_absorbed_by_bound :
    ¬ ∀ a b : Real, (a = b ∧ 2 * Real.log 5 ≤ b) ↔ (2 * Real.log 5 ≤ b) := by
  intro h
  have h0 : (0 : Real) = 2 * Real.log 5 :=
    ((h 0 (2 * Real.log 5)).mpr (le_refl _)).1
  have hpos : 0 < Real.log (5 : Real) := Real.log_pos (by norm_num)
  linarith

/-! ## 5. Conditional assembly of `PaperUnconditionalData` -/

/-- Conditional assembly of the full paper data from the two-field interface.
`hq` supplies `sourceLink.qPilotLogVolume_eq_paper`; `hcomp` is *derived*
from the numeric residual (Section 3), not assumed.  All other fields are the
actual S2678 data (concrete q-pilot object, actual signed hull, actual
Theta-link). -/
noncomputable def paperUnconditionalData_of_hqHcompResidual
    (hnormal : SignedHnormal (l := l) (V := FinitePrimePlace 2 7) (I := I)
      places tuple mu D)
    (R : HqHcompResidual (l := l) (I := I) (T := T) (D := D)) :
    PaperUnconditionalData (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      (I := I) (G := ConcreteKummerGroup (l := l))
      (envStrip := concreteQPilotStrip (l := l))
      (X := PaperC6Carrier places tuple)
      (label := SignedLabel l.value) v
      (O (l := l) (I := I))
      (hull (l := l) (I := I) places tuple mu D hnormal)
      (C3 (l := l) (I := I) (D := D)) :=
  paperUnconditionalData_of_hcomp (l := l) (I := I) (places := places)
    (tuple := tuple) (mu := mu) (D := D) (v := v) (hnormal := hnormal)
    (hq := hq_eq_paperQPilotLogVolume (l := l) (I := I) (T := T) (D := D) R)
    (hcomp := concreteSourceComparison_of_hqHcompResidual (l := l) (I := I)
      (T := T) (places := places) (tuple := tuple) (mu := mu) (D := D)
      (hnormal := hnormal) R)

/-- The same assembly at `l = 5` from the literal numeric residual
`2 log 5 <= sourceBadQAbsLog I.initial`. -/
noncomputable def paperUnconditionalData_five_of_two_log5
    (hnormal : SignedHnormal (l := l) (V := FinitePrimePlace 2 7) (I := I)
      places tuple mu D)
    (hl : l.value = 5)
    (hq : S2678ConcreteSourceQIdentification (I := I) (C3 (l := l) (I := I) (D := D)))
    (h : 2 * Real.log 5 ≤ sourceBadQAbsLog I.initial) :
    PaperUnconditionalData (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      (I := I) (G := ConcreteKummerGroup (l := l))
      (envStrip := concreteQPilotStrip (l := l))
      (X := PaperC6Carrier places tuple)
      (label := SignedLabel l.value) v
      (O (l := l) (I := I))
      (hull (l := l) (I := I) places tuple mu D hnormal)
      (C3 (l := l) (I := I) (D := D)) :=
  paperUnconditionalData_of_hqHcompResidual (l := l) (I := I) (T := T)
    (places := places) (tuple := tuple) (mu := mu) (D := D) (v := v)
    (hnormal := hnormal)
    ⟨hq, (numericResidual_iff_two_log5_five (l := l) (I := I) hl).mpr h⟩

/-- The same assembly at `l = 5` from the native residual `HcompBadQData T`
(plus the index alignment). -/
noncomputable def paperUnconditionalData_five_of_hcompBadQData
    (hnormal : SignedHnormal (l := l) (V := FinitePrimePlace 2 7) (I := I)
      places tuple mu D)
    [Fintype (Bad (nativePlaceSelection T))]
    (hl : l.value = 5)
    (halign : S2678BadQAbsLogAlignment (l := l) (I := I) T)
    (hq : S2678ConcreteSourceQIdentification (I := I) (C3 (l := l) (I := I) (D := D)))
    (hbad : S2681HcompMinimalInputActual.HcompBadQData T) :
    PaperUnconditionalData (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      (I := I) (G := ConcreteKummerGroup (l := l))
      (envStrip := concreteQPilotStrip (l := l))
      (X := PaperC6Carrier places tuple)
      (label := SignedLabel l.value) v
      (O (l := l) (I := I))
      (hull (l := l) (I := I) places tuple mu D hnormal)
      (C3 (l := l) (I := I) (D := D)) :=
  paperUnconditionalData_of_hqHcompResidual (l := l) (I := I) (T := T)
    (places := places) (tuple := tuple) (mu := mu) (D := D) (v := v)
    (hnormal := hnormal)
    (hqHcompResidual_of_native_five (l := l) (I := I) (T := T) (D := D)
      (hq := hq) (hl := hl) (halign := halign) (hbad := hbad))

/-! ## 6. Exact relation to the S2681 minimal input (at `l = 5`) -/

/-- At `l = 5`, the S2681 minimal input plus the source q identification
gives the two-field interface. -/
theorem hqHcompResidual_of_minimalInput_five
    (hq : S2678ConcreteSourceQIdentification (I := I) (C3 (l := l) (I := I) (D := D)))
    [Fintype (Bad (nativePlaceSelection T))]
    (hl : l.value = 5)
    (H : S2681HcompMinimalInputActual.HcompMinimalInput (l := l) (I := I) (T := T)) :
    HqHcompResidual (l := l) (I := I) (T := T) (D := D) := by
  refine ⟨hq, ?_⟩
  show Real.log 5 * (sourceThetaWeightSum l / (c3ThetaCard (l := l) : Real)) ≤
    sourceBadQAbsLog I.initial
  rw [S2681HcompMinimalInputActual.weightSum_div_card_eq_two_of_value_eq_five
    (l := l) hl, mul_comm (Real.log 5) 2]
  exact S2681HcompMinimalInputActual.two_log5_le_sourceBadQAbsLog (l := l)
    (I := I) T H.sourceQ.alignment H.badQ

/-- At `l = 5`, the two-field interface plus the disjoint Tate input and the
source q/order agreement gives the S2681 minimal input (with `hcomp` converted
into `HcompBadQData T`). -/
theorem hcompMinimalInput_of_hqHcompResidual_five
    (R : HqHcompResidual (l := l) (I := I) (T := T) (D := D))
    [Fintype (Bad (nativePlaceSelection T))]
    (hl : l.value = 5)
    (tate : S2681HcompMinimalInputActual.HcompTateInput (l := l) T)
    (hQ : S2681HcompMinimalInputActual.HcompSourceQAgreement (l := l)
      (I := I) (T := T)) :
    S2681HcompMinimalInputActual.HcompMinimalInput (l := l) (I := I) (T := T) := by
  have htwo : 2 * Real.log 5 ≤ sourceBadQAbsLog I.initial :=
    (numericResidual_iff_two_log5_five (l := l) (I := I) hl).mp R.hcomp
  have hbad : S2681HcompMinimalInputActual.HcompBadQData T := by
    unfold S2681HcompMinimalInputActual.HcompBadQData
    rwa [S2681HcompMinimalInputActual.sourceBadQAbsLog_eq_baseQTotalLogMagnitude
      (l := l) (I := I) T hQ.alignment] at htwo
  exact ⟨tate, hQ, hbad⟩

/-! ## 7. The disjoint third residual: the analytic Tate input

The Tate input is a residual of a different kind: S2682 splits the
curve-indexed contract into the coordinate half (constructed at the source
section K-place from the actual S1493 transport) and the analytic half (the
gap).  S2680 records the conditional D4 Tate-q identification.  None of these
statements mentions `C3`, `sourceBadQAbsLog` or `paperQParameter`, so they
are independent of both residuals of Section 1; and S2681's
`hcomp_of_agreement_badQ` shows the numeric comparison does not consume
them. -/

/-- S2682's exact split: the full curve-indexed Tate contract is inhabited iff
both halves are. -/
theorem tateUniformization_split_iff
    {F : Type} [Field F] [NumberField F]
    {X : PuncturedEllipticCurve F}
    {place : NumberField.FinitePlace F}
    {parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place} :
    Nonempty (CurveIndexedTateUniformization X place parameter) ↔
      Nonempty (CurveIndexedTateUniformizationCoordinate X place parameter) ∧
        Nonempty (CurveIndexedTateUniformizationAnalytic X place parameter) :=
  S2682CurveIndexedTateSplitActual.split_iff

/-- S2682's conditional assembly: the actual coordinate half plus the explicit
analytic gap give the full contract. -/
noncomputable def tateUniformization_of_coordinate_and_gap
    {F : Type} [Field F] [NumberField F]
    {X : PuncturedEllipticCurve F}
    {place : NumberField.FinitePlace F}
    {parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place}
    (coordinate : CurveIndexedTateUniformizationCoordinate X place parameter)
    (gap : CurveIndexedTateUniformizationAnalyticGap X place parameter) :
    CurveIndexedTateUniformization X place parameter :=
  S2682CurveIndexedTateSplitActual.full_of_coordinate_of_gap coordinate gap

/-- The coordinate half is constructed (not assumed) at the source section
K-place from the actual S1493 curve transport. -/
theorem coordinate_half_at_sectionKPlace
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    Nonempty (CurveIndexedTateUniformizationCoordinate (kSideCurve (T := T))
      (sectionKPlace T b) (sectionQ T b)) :=
  S2682CurveIndexedTateSplitActual.nonempty_coordinate_atSection T b

/-- S2680's conditional D4 Tate-q identification: on the section order agreement
and the fibre uniformity of the actual card, the frozen statement holds.  Both
hypotheses are T-side; neither mentions the paper q scalar. -/
theorem tateQIdentificationStatement_of_sectionAgreement
    (T : SourceNativeInitialThetaData.{0} l)
    (hagree : ∀ b : Bad (nativePlaceSelection T),
      (sectionFQ T b).order = (badPlaceQCandidate (nativePlaceSelection T) b).order)
    (hfib : FKDescentFiberUniformityStatement (nativePlaceSelection T)
      (S2680TateQIdentificationAssemblyActual.nativeTateUniformizationCard T)) :
    TateQIdentificationStatement (nativePlaceSelection T)
      (S2680TateQIdentificationAssemblyActual.nativeTateUniformizationCard T) :=
  S2680TateQIdentificationAssemblyActual.tateQIdentificationStatement_of_sectionAgreement
    T hagree hfib

/-! ## 8. Axiom audit -/

#print axioms sourceQIdentification_iff_abs_paperQParameter
#print axioms hq_eq_paperQPilotLogVolume
#print axioms concreteSourceComparison_of_numericResidual
#print axioms concreteSourceComparison_of_hqHcompResidual
#print axioms numericResidual_iff_two_log5_five
#print axioms concreteSourceComparison_five_of_two_log5
#print axioms hcompBadQData_iff_comparison_five
#print axioms numericResidual_iff_hcompBadQData_five
#print axioms hqHcompResidual_of_native_five
#print axioms hcompBadQData_of_hqHcompResidual_five
#print axioms paperQParameter_of_hqHcompResidual
#print axioms hqHcompResidual_of_paperQParameter
#print axioms identity_not_absorbed_by_bound
#print axioms paperUnconditionalData_of_hqHcompResidual
#print axioms paperUnconditionalData_five_of_two_log5
#print axioms paperUnconditionalData_five_of_hcompBadQData
#print axioms hqHcompResidual_of_minimalInput_five
#print axioms hcompMinimalInput_of_hqHcompResidual_five
#print axioms tateUniformization_split_iff
#print axioms tateUniformization_of_coordinate_and_gap
#print axioms coordinate_half_at_sectionKPlace
#print axioms tateQIdentificationStatement_of_sectionAgreement

end LeanFormal.IUT.XiFPaper.S2687HqHcompDisjointAnalysisActual
end
