import tmp.sheaf.xif.PaperQPilotObject
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# S2708: the paper-faithful multi-place q-pilot donor

## Layer and consumers

Source q-pilot scalar layer of paper Corollary 3.12.  Consumers:
tmp/sheaf/xif/PaperQPilotObject.lean (PaperQPilotObject.qPilotLogVolume,
qPilotLogVolume_eq), S2706DirectHcompActual,
S2678PaperUnconditionalHcompActual, S2686PaperConcreteHqHcompActual,
S2707PaperUnconditionalActual.

## Paper definition

IUT I, Definition 3.1 supplies the bad-place index V^bad_mod and, for every
bad place b, a local q-parameter q_b; the q-pilot log-volume is the negative
sum of the local log magnitudes over **all** bad places,
-sum_{b in V^bad_mod} |log q_b|, not the log of a single C3.q.

The current source contract SourceDefinition31Data l
(LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean:667) stores
badPlaces : Type and a **Real-valued** family
reduction.qParameter : badPlaces → Real.  It has no field mapping a bad place
to a number-field finite place and no completion element.  The donor below is
therefore the paper-faithful *Real-valued* multi-place object: its qFamily is
definitionally the actual source q-parameter family.

## What is actual here

* MultiPlaceQPilotDonor I: qFamily : I.initial.badPlaces → Real with
  qFamily_eq : qFamily = I.initial.reduction.qParameter.  It is inhabited
  definitionally (MultiPlaceQPilotDonor.ofSource).
* paperQPilotLogVolume_multi D = - sum_b |log (D.qFamily b)|, summed over the
  actual finite bad index I.initial.bad_finite (no single-place substitution,
  no abstract carrier).
* paperQPilotLogVolume_multi_eq_sourceQPilotSignedLog,
  paperQPilotLogVolume_multi_eq_neg_sourceBadQAbsLog.
* HqMulti, hqMulti_holds, hqMulti_iff_badQAbsLog: the migrated hq is
  definitional in the multi-place donor and equivalent to the source bad-q
  absolute-log identity.
* paperQPilotObject_multi: field update of PaperQPilotObject replacing
  qPilotLogVolume by paperQPilotLogVolume_multi D and qPilotLogVolume_eq by its
  identification theorem.

## Exact object gap: FinitePlaceQPilotDonor

The genuinely paper-faithful per-place object needs a finite-place realization
of every abstract bad index,

  placeOf : I.initial.badPlaces → NumberField.FinitePlace I.initial.arithmetic.Fmod

and actual completion elements
qFamily b : FinitePlaceQCandidate (placeOf b) with
localLogMagnitude (qFamily b) = |log (qParameter b)|.

SourceDefinition31Data supplies none of this: badPlaces is an abstract Type,
qParameter is a Real, and no field mentions NumberField.FinitePlace.  Hence
FinitePlaceQPilotDonor cannot be built from the current source contract
without adding placeOf (and the per-place completion data).  This file defines
the structure, proves the conditional transfer to the multi-place volume, and
proves the honest obstruction: the q-candidate log is discrete,
|log q_b| = n_b * log (residueNormBase (placeOf b)) with 0 < n_b, so a donor
can exist only if the Real source family satisfies that discrete condition for
the chosen place map.  No place map is added to SourceDefinition31Data and no
inhabitant is fabricated.

## Consumer migration (qPilotLogVolume_eq → multi-place)

* PaperQPilotObject.qPilotLogVolume_eq: use paperQPilotObject_multi (scalar
  field becomes paperQPilotLogVolume_multi D) or
  paperQPilotObject_qPilotLogVolume_eq_multi for the projection equality.
* S2678ConcreteSourceQIdentification (S2678PaperUnconditionalHcompActual),
  S2686HqResidual (S2686PaperConcreteHqHcompActual), and the hq argument of
  S2707PaperUnconditionalActual: replace the single-q statement
  sourceQPilotSignedLog I.initial = localSignedLog C3.q by HqMulti D.
  HqMulti D holds definitionally (hqMulti_holds) and contains no single C3.q;
  the link back to localSignedLog C3.q is not recoverable, which is exactly
  the wrong single-q object being removed.
* concreteQLogIdentification
  (ConcretePaperUnconditionalDataUnconditionalActual): replace by HqMulti D.
  A remaining bridge to localSignedLog C3.q would require a
  FinitePlaceQPilotDonor plus the single-q normalization identity; that is the
  exact gap above, not an assumption made here.

No sorry, no axiom, no native_decide, no True, no fabricated place map is used.
No existing file is modified.
-/

noncomputable section
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT
namespace Theorem311Source

universe ua uv upi umon ui uG uL uC

open ArithmeticQPilotLogVolume ArithmeticQPilotBaseChange

/-! ## 1. The Real-valued multi-place q-pilot donor -/

/-- The paper-faithful multi-place q-pilot donor over the actual Definition 3.1
source contract: one q-parameter for every bad place, definitionally the actual
source family reduction.qParameter.  The Real codomain is forced by the current
source contract; see FinitePlaceQPilotDonor for the missing finite-place
realization. -/
structure MultiPlaceQPilotDonor
    {l : PrimeGeFive} {V : Type uv}
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  /-- The q-parameter at every bad place of the actual source datum. -/
  qFamily : I.initial.badPlaces → Real
  /-- It is the actual source q-parameter family, not an arbitrary replacement. -/
  qFamily_eq : qFamily = I.initial.reduction.qParameter

namespace MultiPlaceQPilotDonor

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The canonical donor: the actual source q-parameter family itself. -/
noncomputable def ofSource : MultiPlaceQPilotDonor I where
  qFamily := I.initial.reduction.qParameter
  qFamily_eq := rfl

@[simp] theorem ofSource_qFamily (b : I.initial.badPlaces) :
    (ofSource (I := I)).qFamily b = I.initial.reduction.qParameter b := rfl

end MultiPlaceQPilotDonor

/-! ## 2. The multi-place q-pilot log-volume -/

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The paper q-pilot log-volume of a multi-place donor: minus the sum over the
actual finite bad index of the absolute logs of the per-place q-parameters. -/
noncomputable def paperQPilotLogVolume_multi
    (D : MultiPlaceQPilotDonor I) : Real := by
  classical
  letI : Fintype I.initial.badPlaces := I.initial.bad_finite
  exact -(∑ b : I.initial.badPlaces, |Real.log (D.qFamily b)|)

/-- The multi-place volume is the actual source signed q-pilot log. -/
theorem paperQPilotLogVolume_multi_eq_sourceQPilotSignedLog
    (D : MultiPlaceQPilotDonor I) :
    paperQPilotLogVolume_multi D = sourceQPilotSignedLog I.initial := by
  unfold paperQPilotLogVolume_multi sourceQPilotSignedLog sourceBadQAbsLog
  letI : Fintype I.initial.badPlaces := I.initial.bad_finite
  rw [D.qFamily_eq]

/-- The multi-place volume is the negative source bad-q absolute log. -/
theorem paperQPilotLogVolume_multi_eq_neg_sourceBadQAbsLog
    (D : MultiPlaceQPilotDonor I) :
    paperQPilotLogVolume_multi D = -sourceBadQAbsLog I.initial := by
  rw [paperQPilotLogVolume_multi_eq_sourceQPilotSignedLog]
  rfl

/-- The negated multi-place volume is the source bad-q absolute log. -/
theorem neg_paperQPilotLogVolume_multi_eq_sourceBadQAbsLog
    (D : MultiPlaceQPilotDonor I) :
    -paperQPilotLogVolume_multi D = sourceBadQAbsLog I.initial := by
  rw [paperQPilotLogVolume_multi_eq_neg_sourceBadQAbsLog, neg_neg]

/-- The multi-place volume is nonpositive, as a sum of absolute logs. -/
theorem paperQPilotLogVolume_multi_nonpos
    (D : MultiPlaceQPilotDonor I) : paperQPilotLogVolume_multi D ≤ 0 := by
  rw [paperQPilotLogVolume_multi_eq_sourceQPilotSignedLog]
  exact sourceQPilotSignedLog_nonpos I.initial

@[simp] theorem paperQPilotLogVolume_multi_ofSource :
    paperQPilotLogVolume_multi (MultiPlaceQPilotDonor.ofSource (I := I)) =
      sourceQPilotSignedLog I.initial :=
  paperQPilotLogVolume_multi_eq_sourceQPilotSignedLog
    (D := MultiPlaceQPilotDonor.ofSource (I := I))

/-! ## 3. The migrated hq -/

/-- The migrated q-side identification: the global source q-pilot signed scalar
equals the multi-place q-pilot log-volume.  This replaces the single-C3.q form
sourceQPilotSignedLog I.initial = localSignedLog C3.q. -/
def HqMulti (D : MultiPlaceQPilotDonor I) : Prop :=
  sourceQPilotSignedLog I.initial = paperQPilotLogVolume_multi D

/-- HqMulti holds for every multi-place donor: it is the definitional
identification of the source family with itself. -/
theorem hqMulti_holds (D : MultiPlaceQPilotDonor I) : HqMulti D := by
  unfold HqMulti
  exact (paperQPilotLogVolume_multi_eq_sourceQPilotSignedLog D).symm

/-- HqMulti is exactly the source bad-q absolute-log identity; no single C3.q
occurs. -/
theorem hqMulti_iff_badQAbsLog (D : MultiPlaceQPilotDonor I) :
    HqMulti D ↔
      sourceQPilotSignedLog I.initial = -sourceBadQAbsLog I.initial := by
  unfold HqMulti
  rw [paperQPilotLogVolume_multi_eq_neg_sourceBadQAbsLog]

/-- HqMulti in the orientation used by the paper q-pilot scalar. -/
theorem hqMulti_iff_volume_eq (D : MultiPlaceQPilotDonor I) :
    HqMulti D ↔ paperQPilotLogVolume_multi D = sourceQPilotSignedLog I.initial := by
  unfold HqMulti
  exact eq_comm

/-- HqMulti for the canonical donor (the actual source family). -/
theorem hqMulti_ofSource : HqMulti (MultiPlaceQPilotDonor.ofSource (I := I)) :=
  hqMulti_holds _

/-! ## 4. Migration of PaperQPilotObject -/

/-- The projection equality: any paper q-pilot object with the source scalar
has q-pilot log-volume equal to the multi-place volume of any donor. -/
theorem paperQPilotObject_qPilotLogVolume_eq_multi
    {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
    {G : Type uG} [Group G] [TopologicalSpace G]
    {envStrip : FPrimeStrip V}
    (O : PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
      I G envStrip)
    (D : MultiPlaceQPilotDonor I) :
    O.qPilotLogVolume = paperQPilotLogVolume_multi D := by
  rw [O.qPilotLogVolume_eq, paperQPilotLogVolume_multi_eq_sourceQPilotSignedLog]

/-- The migrated object: all structural fields of O are kept and the scalar
field is replaced by the multi-place q-pilot log-volume with its
identification proof. -/
noncomputable def paperQPilotObject_multi
    {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
    {G : Type uG} [Group G] [TopologicalSpace G]
    {envStrip : FPrimeStrip V}
    (O : PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
      I G envStrip)
    (D : MultiPlaceQPilotDonor I) :
    PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
      I G envStrip :=
  { O with
    qPilotLogVolume := paperQPilotLogVolume_multi D
    qPilotLogVolume_eq :=
      paperQPilotLogVolume_multi_eq_sourceQPilotSignedLog D }

/-- The migrated object's scalar is the multi-place volume. -/
@[simp] theorem paperQPilotObject_multi_qPilotLogVolume
    {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
    {G : Type uG} [Group G] [TopologicalSpace G]
    {envStrip : FPrimeStrip V}
    (O : PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
      I G envStrip)
    (D : MultiPlaceQPilotDonor I) :
    (paperQPilotObject_multi O D).qPilotLogVolume =
      paperQPilotLogVolume_multi D := rfl

/-! ## 5. The paper-faithful finite-place donor and its exact gap -/

/-- The paper-faithful per-place q-pilot donor.  It is NOT derivable from the
current SourceDefinition31Data: it requires a new field placeOf (a map from the
abstract bad-place index to number-field finite places) together with actual
completion q-candidates whose local log magnitudes are the source q-parameter
absolute logs.  This structure records exactly that missing source data; it is
not inhabited in this file. -/
structure FinitePlaceQPilotDonor
    {l : PrimeGeFive} {V : Type uv}
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  /-- The missing source field: a finite-place realization of every bad index. -/
  placeOf : I.initial.badPlaces →
    NumberField.FinitePlace I.initial.arithmetic.Fmod
  /-- The actual local q-candidate at each realized bad place. -/
  qFamily : (b : I.initial.badPlaces) →
    NumberFieldFinitePlace.FinitePlaceQCandidate (placeOf b)
  /-- The per-place realization of the source q-parameter absolute log. -/
  qFamily_log_eq : ∀ b : I.initial.badPlaces,
    localLogMagnitude (qFamily b) =
      |Real.log (I.initial.reduction.qParameter b)|

/-- The q-pilot log-volume of a finite-place donor: the same multi-place sum,
now computed from actual completion elements. -/
noncomputable def paperQPilotLogVolume_finitePlace
    (D : FinitePlaceQPilotDonor I) : Real := by
  classical
  letI : Fintype I.initial.badPlaces := I.initial.bad_finite
  exact -(∑ b : I.initial.badPlaces, localLogMagnitude (D.qFamily b))

/-- Conditionally (on the missing finite-place data) the paper-faithful volume
is the actual source signed q-pilot log. -/
theorem paperQPilotLogVolume_finitePlace_eq_sourceQPilotSignedLog
    (D : FinitePlaceQPilotDonor I) :
    paperQPilotLogVolume_finitePlace D = sourceQPilotSignedLog I.initial := by
  unfold paperQPilotLogVolume_finitePlace sourceQPilotSignedLog sourceBadQAbsLog
  letI : Fintype I.initial.badPlaces := I.initial.bad_finite
  congr 1
  exact Finset.sum_congr rfl (fun b _ => D.qFamily_log_eq b)

/-- Conditionally the paper-faithful volume is the negative source bad-q
absolute log. -/
theorem paperQPilotLogVolume_finitePlace_eq_neg_sourceBadQAbsLog
    (D : FinitePlaceQPilotDonor I) :
    paperQPilotLogVolume_finitePlace D = -sourceBadQAbsLog I.initial := by
  rw [paperQPilotLogVolume_finitePlace_eq_sourceQPilotSignedLog]
  rfl

/-- Conditional bridge: once the finite-place realization ∃, its volume is
the multi-place volume of the canonical Real-valued donor. -/
theorem paperQPilotLogVolume_finitePlace_eq_multi
    (D : FinitePlaceQPilotDonor I) :
    paperQPilotLogVolume_finitePlace D =
      paperQPilotLogVolume_multi (MultiPlaceQPilotDonor.ofSource (I := I)) := by
  rw [paperQPilotLogVolume_finitePlace_eq_sourceQPilotSignedLog,
    paperQPilotLogVolume_multi_eq_sourceQPilotSignedLog]

/-- **The exact obstruction.**  The necessary discrete form of the source
q-parameter: a finite-place realization forces
|log q_b| = n_b * log (residueNormBase (placeOf b)) with 0 < n_b.  Thus the
generic Real family qParameter admits a FinitePlaceQPilotDonor only when it lies
in this discrete set for the chosen place map. -/
theorem finitePlaceQPilotDonor_qParameter_discrete
    (D : FinitePlaceQPilotDonor I) (b : I.initial.badPlaces) :
    ∃ n : Nat, 0 < n ∧
      |Real.log (I.initial.reduction.qParameter b)| =
        (n : Real) * Real.log (residueNormBase (D.placeOf b)) := by
  refine ⟨(D.qFamily b).order, (D.qFamily b).order_pos, ?_⟩
  rw [← D.qFamily_log_eq b, localLogMagnitude_eq_order_mul_log]

/-- **The no-go criterion.**  If for every candidate place map some bad place
violates the discrete log condition, then no FinitePlaceQPilotDonor ∃.
This is the honest statement of the missing source data: the Real contract
alone does not supply a finite-place realization. -/
theorem not_nonempty_finitePlaceQPilotDonor_of_obstruction
    (h : ∀ placeOf : I.initial.badPlaces →
        NumberField.FinitePlace I.initial.arithmetic.Fmod,
      ∃ b : I.initial.badPlaces, ∀ n : Nat, 0 < n →
        |Real.log (I.initial.reduction.qParameter b)| ≠
          (n : Real) * Real.log (residueNormBase (placeOf b))) :
    ¬ Nonempty (FinitePlaceQPilotDonor I) := by
  rintro ⟨D⟩
  obtain ⟨b, hb⟩ := h D.placeOf
  obtain ⟨n, hn, heq⟩ := finitePlaceQPilotDonor_qParameter_discrete D b
  exact hb n hn heq

/-- Once the missing finite-place data is supplied, the same object migration
gives the paper-faithful scalar on a PaperQPilotObject. -/
theorem paperQPilotObject_qPilotLogVolume_eq_finitePlace
    {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
    {G : Type uG} [Group G] [TopologicalSpace G]
    {envStrip : FPrimeStrip V}
    (O : PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
      I G envStrip)
    (D : FinitePlaceQPilotDonor I) :
    O.qPilotLogVolume = paperQPilotLogVolume_finitePlace D := by
  rw [O.qPilotLogVolume_eq,
    paperQPilotLogVolume_finitePlace_eq_sourceQPilotSignedLog]

/-! ## 6. Axiom audit -/

#check MultiPlaceQPilotDonor
#check MultiPlaceQPilotDonor.ofSource
#check paperQPilotLogVolume_multi
#check paperQPilotLogVolume_multi_eq_sourceQPilotSignedLog
#check paperQPilotLogVolume_multi_eq_neg_sourceBadQAbsLog
#check HqMulti
#check hqMulti_holds
#check hqMulti_iff_badQAbsLog
#check paperQPilotObject_qPilotLogVolume_eq_multi
#check paperQPilotObject_multi
#check FinitePlaceQPilotDonor
#check paperQPilotLogVolume_finitePlace
#check paperQPilotLogVolume_finitePlace_eq_sourceQPilotSignedLog
#check finitePlaceQPilotDonor_qParameter_discrete
#check not_nonempty_finitePlaceQPilotDonor_of_obstruction

#print axioms paperQPilotLogVolume_multi_eq_sourceQPilotSignedLog
#print axioms paperQPilotLogVolume_multi_eq_neg_sourceBadQAbsLog
#print axioms neg_paperQPilotLogVolume_multi_eq_sourceBadQAbsLog
#print axioms paperQPilotLogVolume_multi_nonpos
#print axioms paperQPilotLogVolume_multi_ofSource
#print axioms hqMulti_holds
#print axioms hqMulti_iff_badQAbsLog
#print axioms hqMulti_iff_volume_eq
#print axioms hqMulti_ofSource
#print axioms paperQPilotObject_qPilotLogVolume_eq_multi
#print axioms paperQPilotObject_multi_qPilotLogVolume
#print axioms paperQPilotLogVolume_finitePlace_eq_sourceQPilotSignedLog
#print axioms paperQPilotLogVolume_finitePlace_eq_neg_sourceBadQAbsLog
#print axioms paperQPilotLogVolume_finitePlace_eq_multi
#print axioms finitePlaceQPilotDonor_qParameter_discrete
#print axioms not_nonempty_finitePlaceQPilotDonor_of_obstruction
#print axioms paperQPilotObject_qPilotLogVolume_eq_finitePlace

end Theorem311Source
end LeanFormal.IUT

end
