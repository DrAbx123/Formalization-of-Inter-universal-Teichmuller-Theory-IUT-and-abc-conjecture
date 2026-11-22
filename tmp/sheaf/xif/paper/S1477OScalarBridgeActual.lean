import tmp.sheaf.xif.paper.OrigXiFThetaLinkActual
import tmp.sheaf.xif.paper.S1415MarkedTraceActual

/-!
# S1477: O-layer scalar bridge from the actual S1415 marked trace / S1136 / source hull

Layer: O (original-text Theta-link).  This file attempts to construct the two
exact scalar fields of OrigXiFThetaLinkActual (S1463),

  scalar_eq : O.qPilotLogVolume = OrigXiFPaperQPilotLogVolume C3
  signedHull_le : OrigXiFPaperQPilotLogVolume C3 <= OrigXiFSignedThetaHullLogVolume D,

from the actual S1415 marked trace, the S1136 monotone-gluing skeleton, and the
source hull.  It does not assert an inhabitant of the O structure and it does
not use the target field as an input.

## Exact reductions

* OrigXiFOScalarExactField is exactly
  -sourceBadQAbsLog I.initial = Real.log ‖C3.q.q‖ (equivalently the
  -|log| form).  The S1415 q-mark readout is
  I.sourceQPilotLogVolume v R n = card(SourceVolumeIndex l) * log q_source,
  a different scalar: scalar_eq needs a separate O-to-source readout
  identification.  In the empty-bad-place regime -sourceBadQAbsLog = 0 while
  log ‖C3.q.q‖ < 0, so scalar_eq is actually refutable there; it is a
  branch obstruction, not a theorem of the interface.

* OrigXiFSignedHullExactField is exactly
  D.determinant.procession.average <= |Real.log ‖C3.q.q‖|, i.e. the actual
  signed hull magnitude is at most the actual C3 q magnitude.  S1415 only
  proves the value-layer comparison
  I.sourceQPilotLogVolume v R n <= I.sourceThetaHullLogVolume v R n.

## S1136

With the identity glue, any S1136 datum whose qPilotLog/hullLog are the actual
O scalars has theta_le exactly the O comparison; using it would take the
target as input.  For a non-identity glue, the existence of a monotone glue
carrying the two source readouts to the two O readouts is equivalent to the O
comparison whenever the source comparison is strict.  Thus S1136 does not add
independent content; the missing datum is the source-readout identification,
not another scalar wrapper.

## What is proved positively

* Under the two explicit source-readout alignments, S1415 implies the O
  comparison, and the two are equivalent; this is the exact conditional
  bridge and it factors through the S1136 data built in
  s1136DataOfSourceAlignment.
* Independently of S1415 and of D, if the actual C3 q-pilot scalar is at most
  -1, then signedHull_le holds for every actual D, because the actual signed
  theta hull log-volume is bounded below by -1.

No placeholder proof, extra assumption, or arbitrary inhabitant is used.
All conditional fields are named exact propositions, not hidden assumptions.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1477OScalarBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.OrigXiF
open LeanFormal.IUT.XiFPaper.OrigXiFPaperQPilotScalarActual
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.XiFPaper.S1136SourceComparisonViaGluingActual
open LeanFormal.IUT.XiFPaper.S1415MarkedTraceActual

universe u uG uL uC

variable {l : PrimeGeFive} {X : Type u} [TopologicalSpace X]
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable (v : FinitePrimePlace 2 7)
variable (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip (FinitePrimePlace 2 7)}
variable (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
variable (D : OrigXiFPaperSignedHullData X l)
variable (C3 : SourcePilotRegionDataL (I := I))

/-! ## 1. The two exact O-layer scalar fields -/

/-- The exact first scalar field of S1463, as a named proposition. -/
def OrigXiFOScalarExactField
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (C3 : SourcePilotRegionDataL (I := I)) : Prop :=
  O.qPilotLogVolume = OrigXiFPaperQPilotLogVolume C3

/-- The exact signed-hull comparison field of S1463, as a named proposition. -/
def OrigXiFOSignedHullExactField
    (D : OrigXiFPaperSignedHullData X l)
    (C3 : SourcePilotRegionDataL (I := I)) : Prop :=
  OrigXiFPaperQPilotLogVolume C3 <= OrigXiFSignedThetaHullLogVolume D

theorem origXiFOScalarExactField_def
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (C3 : SourcePilotRegionDataL (I := I)) :
    OrigXiFOScalarExactField I O C3 =
      (O.qPilotLogVolume = OrigXiFPaperQPilotLogVolume C3) := rfl

theorem origXiFOSignedHullExactField_def
    (D : OrigXiFPaperSignedHullData X l)
    (C3 : SourcePilotRegionDataL (I := I)) :
    OrigXiFOSignedHullExactField I D C3 =
      (OrigXiFPaperQPilotLogVolume C3 <= OrigXiFSignedThetaHullLogVolume D) := rfl

/-! ## 2. Exact reduction of scalar_eq -/

/-- The object field is the source bad-place absolute-log sum, so scalar_eq is
exactly the equality of that sum with the actual C3 completion log. -/
theorem origXiFOScalarExactField_iff_badQAbsLog
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (C3 : SourcePilotRegionDataL (I := I)) :
    OrigXiFOScalarExactField I O C3 ↔
      -sourceBadQAbsLog I.initial = Real.log ‖C3.q.q‖ := by
  unfold OrigXiFOScalarExactField
  rw [O.qPilotLogVolume_eq, OrigXiFPaperQPilotLogVolume_eq_log_norm]
  rfl

/-- The same exact reduction in the paper -|log| form. -/
theorem origXiFOScalarExactField_iff_badQAbsLog_abs
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (C3 : SourcePilotRegionDataL (I := I)) :
    OrigXiFOScalarExactField I O C3 ↔
      -sourceBadQAbsLog I.initial = -|Real.log ‖C3.q.q‖| := by
  unfold OrigXiFOScalarExactField
  rw [O.qPilotLogVolume_eq, OrigXiFPaperQPilotLogVolume_eq_neg_abs_log_q]
  rfl

/-- The S1415 q-mark readout is the value-layer source q scalar. -/
theorem markedTrace_readout_qMark
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    (readout I v) (qMark I v R n) = I.sourceQPilotLogVolume v R n :=
  readout_qMark I v R n

/-- scalar_eq factorizes through one common value-layer readout: if the O
scalar and the C3 scalar both equal the actual q-mark readout, the exact first
field holds.  The two hypotheses are the missing O-to-source identifications,
not consequences of S1415. -/
theorem origXiFOScalarExactField_of_sameReadout
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (C3 : SourcePilotRegionDataL (I := I))
    (hO : O.qPilotLogVolume = I.sourceQPilotLogVolume v R n)
    (hC3 : OrigXiFPaperQPilotLogVolume C3 = I.sourceQPilotLogVolume v R n) :
    OrigXiFOScalarExactField I O C3 :=
  hO.trans hC3.symm

/-- Conversely, if the O scalar is already the q-mark readout, scalar_eq is
exactly the C3-to-readout identification. -/
theorem origXiFOScalarExactField_iff_sameReadout_of_O
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (C3 : SourcePilotRegionDataL (I := I))
    (hO : O.qPilotLogVolume = I.sourceQPilotLogVolume v R n) :
    OrigXiFOScalarExactField I O C3 ↔
      OrigXiFPaperQPilotLogVolume C3 = I.sourceQPilotLogVolume v R n := by
  unfold OrigXiFOScalarExactField
  rw [hO]
  exact eq_comm

/-- Exact branch refutation: if the source bad-place absolute-log sum is zero,
the object scalar is zero, while the actual C3 completion scalar is strictly
negative.  Hence scalar_eq is not a theorem of the interface. -/
theorem not_origXiFOScalarExactField_of_badQAbsLog_zero
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (C3 : SourcePilotRegionDataL (I := I))
    (hzero : sourceBadQAbsLog I.initial = 0) :
    ¬ OrigXiFOScalarExactField I O C3 := by
  intro h
  have h' := (origXiFOScalarExactField_iff_badQAbsLog I O C3).mp h
  have hlog : Real.log ‖C3.q.q‖ = 0 := by
    rw [← h', hzero, neg_zero]
  have hneg : Real.log ‖C3.q.q‖ < 0 := localSignedLog_neg C3.q
  linarith

/-- The empty-bad-place branch realizes the zero source sum, so scalar_eq
fails there without any additional C3 hypothesis. -/
theorem not_origXiFOScalarExactField_of_no_badPlaces
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (C3 : SourcePilotRegionDataL (I := I))
    [IsEmpty I.initial.badPlaces] :
    ¬ OrigXiFOScalarExactField I O C3 := by
  apply not_origXiFOScalarExactField_of_badQAbsLog_zero I O C3
  unfold sourceBadQAbsLog
  letI := I.initial.bad_finite
  exact Finset.sum_eq_zero (fun b _ => isEmptyElim b)

/-! ## 3. Exact reduction of signedHull_le -/

/-- signedHull_le is exactly the comparison of the actual determinant
procession average with the actual C3 q magnitude. -/
theorem origXiFOSignedHullExactField_iff_processionAverage
    (D : OrigXiFPaperSignedHullData X l)
    (C3 : SourcePilotRegionDataL (I := I)) :
    OrigXiFOSignedHullExactField I D C3 ↔
      D.determinant.procession.average <= -Real.log ‖C3.q.q‖ := by
  unfold OrigXiFOSignedHullExactField
  rw [OrigXiFPaperQPilotLogVolume_eq_log_norm,
    OrigXiFSignedThetaHullLogVolume_eq_neg_average]
  constructor <;> intro h <;> linarith

/-- The same comparison in absolute-value form: the actual signed hull
magnitude is at most the actual C3 q magnitude. -/
theorem origXiFOSignedHullExactField_iff_average_le_magnitude
    (D : OrigXiFPaperSignedHullData X l)
    (C3 : SourcePilotRegionDataL (I := I)) :
    OrigXiFOSignedHullExactField I D C3 ↔
      D.determinant.procession.average <= |Real.log ‖C3.q.q‖| := by
  rw [origXiFOSignedHullExactField_iff_processionAverage]
  have hneg : Real.log ‖C3.q.q‖ < 0 := localSignedLog_neg C3.q
  rw [abs_of_neg hneg]

/-- A source-level sufficient condition, independent of S1415 and of D: if the
actual C3 q-pilot scalar is at most -1, then the actual signed hull log-volume
(which is bounded below by -1) is above it. -/
theorem origXiFOSignedHullExactField_of_qPilotLogVolume_le_neg_one
    (D : OrigXiFPaperSignedHullData X l)
    (C3 : SourcePilotRegionDataL (I := I))
    (h : OrigXiFPaperQPilotLogVolume C3 <= -1) :
    OrigXiFOSignedHullExactField I D C3 :=
  le_trans h (OrigXiFSignedThetaHullLogVolume_ge_neg_one D)

/-- The same sufficient condition in terms of the C3 q magnitude: if the local
log-magnitude is at least one, the O signed-hull comparison holds for every
actual D. -/
theorem origXiFOSignedHullExactField_of_one_le_qMagnitude
    (D : OrigXiFPaperSignedHullData X l)
    (C3 : SourcePilotRegionDataL (I := I))
    (h : 1 <= -Real.log ‖C3.q.q‖) :
    OrigXiFOSignedHullExactField I D C3 := by
  apply origXiFOSignedHullExactField_of_qPilotLogVolume_le_neg_one I D C3
  rw [OrigXiFPaperQPilotLogVolume_eq_log_norm]
  linarith

/-- If the actual procession average is zero, the comparison holds for every
actual C3: the signed hull scalar is zero and the C3 scalar is negative. -/
theorem origXiFOSignedHullExactField_of_average_zero
    (D : OrigXiFPaperSignedHullData X l)
    (C3 : SourcePilotRegionDataL (I := I))
    (h : D.determinant.procession.average = 0) :
    OrigXiFOSignedHullExactField I D C3 := by
  rw [origXiFOSignedHullExactField_iff_processionAverage, h]
  have hneg : Real.log ‖C3.q.q‖ < 0 := localSignedLog_neg C3.q
  linarith

/-- Conditional refutation at the other extremal actual procession value: if
the average is one and the C3 completion log is greater than -1, the O
comparison fails.  This records a concrete branch in which no construction of
the exact field can exist. -/
theorem not_origXiFOSignedHullExactField_of_average_one_of_log_gt_neg_one
    (D : OrigXiFPaperSignedHullData X l)
    (C3 : SourcePilotRegionDataL (I := I))
    (hD : D.determinant.procession.average = 1)
    (hq : -1 < Real.log ‖C3.q.q‖) :
    ¬ OrigXiFOSignedHullExactField I D C3 := by
  intro h
  have h' := (origXiFOSignedHullExactField_iff_processionAverage I D C3).mp h
  rw [hD] at h'
  linarith

/-! ## 4. The S1136 identity-glue loop -/

/-- With the identity glue, an S1136 datum whose q/hull scalars are the actual
O scalars has theta_le exactly the O signed-hull comparison.  Thus the
identity-glue S1136 route cannot supply the target from S1415: it requires the
target itself. -/
theorem s1136_identity_glue_theta_le_iff
    (Dg : S1136GluingData)
    (hglue : Dg.glue = id)
    (hq : Dg.qPilotLog = OrigXiFPaperQPilotLogVolume C3)
    (hh : Dg.hullLog = OrigXiFSignedThetaHullLogVolume D) :
    (Dg.thetaPilotLog <= Dg.thetaHullLog) ↔ OrigXiFOSignedHullExactField I D C3 := by
  have hq_eq : Dg.qPilotLog = Dg.thetaPilotLog := by
    simpa [hglue] using Dg.qPilotLog_eq
  have hh_eq : Dg.hullLog = Dg.thetaHullLog := by
    simpa [hglue] using Dg.hullLog_eq
  unfold OrigXiFOSignedHullExactField
  constructor
  · intro h
    calc
      OrigXiFPaperQPilotLogVolume C3 = Dg.qPilotLog := hq.symm
      _ = Dg.thetaPilotLog := hq_eq
      _ <= Dg.thetaHullLog := h
      _ = Dg.hullLog := hh_eq.symm
      _ = OrigXiFSignedThetaHullLogVolume D := hh
  · intro h
    calc
      Dg.thetaPilotLog = Dg.qPilotLog := hq_eq.symm
      _ = OrigXiFPaperQPilotLogVolume C3 := hq
      _ <= OrigXiFSignedThetaHullLogVolume D := h
      _ = Dg.hullLog := hh.symm
      _ = Dg.thetaHullLog := hh_eq

/-! ## 5. The actual S1415 source-readout route -/

/-- The two exact source-readout alignments needed to transport the S1415
value-layer comparison to the O layer.  These are not supplied by S1415,
S1136, or the source hull construction; they are the exact bridge fields. -/
structure OrigXiFOSourceAlignment
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (v : FinitePrimePlace 2 7) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l)
    (C3 : SourcePilotRegionDataL (I := I))
    (D : OrigXiFPaperSignedHullData X l) : Prop where
  /-- The actual C3 q-pilot scalar is the S1415 q-mark readout. -/
  qPilotLog_eq : OrigXiFPaperQPilotLogVolume C3 = I.sourceQPilotLogVolume v R n
  /-- The actual signed theta hull scalar is the S1415 source hull scalar. -/
  hullLog_eq : OrigXiFSignedThetaHullLogVolume D = I.sourceThetaHullLogVolume v R n

/-- Under the two source-readout alignments, the O comparison and the S1415
value-layer comparison are equivalent. -/
theorem origXiFOSignedHullExactField_iff_sourceComparison_of_alignment
    (A : OrigXiFOSourceAlignment I v R n C3 D) :
    (I.sourceQPilotLogVolume v R n <= I.sourceThetaHullLogVolume v R n) ↔
      OrigXiFOSignedHullExactField I D C3 := by
  unfold OrigXiFOSignedHullExactField
  rw [A.qPilotLog_eq, A.hullLog_eq]

/-- Conditional construction of the O signed-hull field from the actual S1415
first field and the two source-readout alignments. -/
theorem origXiFOSignedHullExactField_of_s1415
    (hBdd : S1415HullReadoutFirstField I v R n)
    (A : OrigXiFOSourceAlignment I v R n C3 D) :
    OrigXiFOSignedHullExactField I D C3 :=
  (origXiFOSignedHullExactField_iff_sourceComparison_of_alignment I v R n D C3 A).mp
    (s1415Comparison_of_firstField_direct I v R n hBdd)

/-- The S1136 data at the actual source readouts, from the S1415 first field and
the two alignments.  The gluing map is the identity: both the source comparison
and the O transport live on the same real line here, and the alignment is the
only bridge. -/
noncomputable def s1136DataOfSourceAlignment
    (hBdd : S1415HullReadoutFirstField I v R n)
    (A : OrigXiFOSourceAlignment I v R n C3 D) : S1136GluingData where
  thetaPilotLog := I.sourceQPilotLogVolume v R n
  thetaHullLog := I.sourceThetaHullLogVolume v R n
  qPilotLog := OrigXiFPaperQPilotLogVolume C3
  hullLog := OrigXiFSignedThetaHullLogVolume D
  glue := id
  glue_mono := fun h => h
  qPilotLog_eq := A.qPilotLog_eq
  hullLog_eq := A.hullLog_eq
  theta_le := s1415Comparison_of_firstField_direct I v R n hBdd

/-- The same conditional construction packaged through the actual S1136
comparison theorem. -/
theorem origXiFOSignedHullExactField_of_s1136_sourceAlignment
    (hBdd : S1415HullReadoutFirstField I v R n)
    (A : OrigXiFOSourceAlignment I v R n C3 D) :
    OrigXiFOSignedHullExactField I D C3 :=
  s1136Comparison (s1136DataOfSourceAlignment I v R n D C3 hBdd A)

/-! ## 6. Monotone gluing without identity: equivalent, not weaker -/

/-- A monotone gluing bridge from the two actual source readouts to the two
actual O readouts.  This is the non-identity-glue form of the S1136 datum. -/
structure OrigXiFOScalarGluingBridge
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (v : FinitePrimePlace 2 7) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l)
    (C3 : SourcePilotRegionDataL (I := I))
    (D : OrigXiFPaperSignedHullData X l) where
  glue : Real → Real
  glue_mono : Monotone glue
  qPilotLog_eq :
    OrigXiFPaperQPilotLogVolume C3 = glue (I.sourceQPilotLogVolume v R n)
  hullLog_eq :
    OrigXiFSignedThetaHullLogVolume D = glue (I.sourceThetaHullLogVolume v R n)

/-- A monotone gluing bridge plus the source comparison constructs the O
signed-hull field. -/
theorem origXiFOSignedHullExactField_of_gluingBridge
    (hcomp : I.sourceQPilotLogVolume v R n <= I.sourceThetaHullLogVolume v R n)
    (B : OrigXiFOScalarGluingBridge I v R n C3 D) :
    OrigXiFOSignedHullExactField I D C3 := by
  unfold OrigXiFOSignedHullExactField
  rw [B.qPilotLog_eq, B.hullLog_eq]
  exact B.glue_mono hcomp

/-- Any S1136 datum whose theta scalars are the source readouts and whose
q/hull scalars are the O scalars gives a monotone gluing bridge.  This is the
precise sense in which S1136 is only a repackaging of the bridge data. -/
noncomputable def gluingBridgeOfS1136
    (Dg : S1136GluingData)
    (hq : Dg.qPilotLog = OrigXiFPaperQPilotLogVolume C3)
    (hh : Dg.hullLog = OrigXiFSignedThetaHullLogVolume D)
    (hqs : Dg.thetaPilotLog = I.sourceQPilotLogVolume v R n)
    (hhs : Dg.thetaHullLog = I.sourceThetaHullLogVolume v R n) :
    OrigXiFOScalarGluingBridge I v R n C3 D where
  glue := Dg.glue
  glue_mono := fun {a b} h => Dg.glue_mono h
  qPilotLog_eq := by
    rw [← hq, Dg.qPilotLog_eq, hqs]
  hullLog_eq := by
    rw [← hh, Dg.hullLog_eq, hhs]

/-- The general S1136 route: source comparison plus four scalar matches gives
the O signed-hull field. -/
theorem origXiFOSignedHullExactField_of_s1136_sourceData
    (Dg : S1136GluingData)
    (hcomp : I.sourceQPilotLogVolume v R n <= I.sourceThetaHullLogVolume v R n)
    (hq : Dg.qPilotLog = OrigXiFPaperQPilotLogVolume C3)
    (hh : Dg.hullLog = OrigXiFSignedThetaHullLogVolume D)
    (hqs : Dg.thetaPilotLog = I.sourceQPilotLogVolume v R n)
    (hhs : Dg.thetaHullLog = I.sourceThetaHullLogVolume v R n) :
    OrigXiFOSignedHullExactField I D C3 :=
  origXiFOSignedHullExactField_of_gluingBridge I v R n D C3 hcomp
    (gluingBridgeOfS1136 I v R n D C3 Dg hq hh hqs hhs)

/-- For two real points a <= b, the existence of a monotone map with
prescribed values is exactly the order relation between those values (with the
degenerate case a = b forcing equality). -/
theorem exists_monotone_pair_iff {a b c d : Real} (hab : a <= b) :
    (∃ f : Real → Real, Monotone f ∧ f a = c ∧ f b = d) ↔
      (a < b ∧ c <= d) ∨ (a = b ∧ c = d) := by
  constructor
  · rintro ⟨f, hf, ha, hb⟩
    rcases lt_or_eq_of_le hab with hlt | heq
    · exact Or.inl ⟨hlt, by rw [← ha, ← hb]; exact hf hlt.le⟩
    · exact Or.inr ⟨heq, by rw [← ha, ← hb, heq]⟩
  · rintro (⟨hlt, hcd⟩ | ⟨heq, hcd⟩)
    · refine ⟨fun x => if x < b then c else d, ?_, ?_, ?_⟩
      · intro x y hxy
        by_cases hy : y < b
        · have hx : x < b := lt_of_le_of_lt hxy hy
          simp [hx, hy]
        · have hfy : (if y < b then c else d) = d := if_neg hy
          change (if x < b then c else d) <= (if y < b then c else d)
          rw [hfy]
          split_ifs with hx
          · exact hcd
          · exact le_rfl
      · show (if a < b then c else d) = c
        rw [if_pos hlt]
      · show (if b < b then c else d) = d
        rw [if_neg (lt_irrefl b)]
    · subst b
      exact ⟨fun _ => c, (fun _ _ _ => le_rfl), rfl, hcd⟩

/-- Given a strict S1415 comparison, the non-identity S1136 bridge exists
exactly when the O signed-hull comparison holds.  Hence S1136 does not reduce
the target to anything weaker; it is equivalent to the target in this branch. -/
theorem nonempty_gluingBridge_iff_of_lt
    (hlt : I.sourceQPilotLogVolume v R n < I.sourceThetaHullLogVolume v R n) :
    Nonempty (OrigXiFOScalarGluingBridge I v R n C3 D) ↔
      OrigXiFOSignedHullExactField I D C3 := by
  constructor
  · rintro ⟨B⟩
    exact origXiFOSignedHullExactField_of_gluingBridge I v R n D C3 hlt.le B
  · intro h
    unfold OrigXiFOSignedHullExactField at h
    have hcases := (exists_monotone_pair_iff
      (a := I.sourceQPilotLogVolume v R n)
      (b := I.sourceThetaHullLogVolume v R n)
      (c := OrigXiFPaperQPilotLogVolume C3)
      (d := OrigXiFSignedThetaHullLogVolume D) hlt.le).mpr
      (Or.inl ⟨hlt, h⟩)
    rcases hcases with ⟨f, hf, hfa, hfb⟩
    exact ⟨{
      glue := f
      glue_mono := hf
      qPilotLog_eq := hfa.symm
      hullLog_eq := hfb.symm }⟩

/-! ## 7. Checks -/

#check OrigXiFOScalarExactField
#check OrigXiFOSignedHullExactField
#check origXiFOScalarExactField_iff_badQAbsLog
#check origXiFOScalarExactField_iff_badQAbsLog_abs
#check origXiFOScalarExactField_of_sameReadout
#check not_origXiFOScalarExactField_of_badQAbsLog_zero
#check not_origXiFOScalarExactField_of_no_badPlaces
#check origXiFOSignedHullExactField_iff_processionAverage
#check origXiFOSignedHullExactField_iff_average_le_magnitude
#check origXiFOSignedHullExactField_of_qPilotLogVolume_le_neg_one
#check origXiFOSignedHullExactField_of_one_le_qMagnitude
#check origXiFOSignedHullExactField_of_average_zero
#check not_origXiFOSignedHullExactField_of_average_one_of_log_gt_neg_one
#check s1136_identity_glue_theta_le_iff
#check OrigXiFOSourceAlignment
#check origXiFOSignedHullExactField_iff_sourceComparison_of_alignment
#check origXiFOSignedHullExactField_of_s1415
#check s1136DataOfSourceAlignment
#check origXiFOSignedHullExactField_of_s1136_sourceAlignment
#check OrigXiFOScalarGluingBridge
#check origXiFOSignedHullExactField_of_gluingBridge
#check gluingBridgeOfS1136
#check origXiFOSignedHullExactField_of_s1136_sourceData
#check exists_monotone_pair_iff
#check nonempty_gluingBridge_iff_of_lt

end LeanFormal.IUT.XiFPaper.S1477OScalarBridgeActual