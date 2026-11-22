import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.n8.closure.SourcePilotRegion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceRelativeCommonPrime
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion

/-!
# Badplace / C3 tensor-index comparison: prime part and exact M1 statements

Source: IUT III, Definition 3.8, (i), p. 112-113: the q-pilot object is
determined by the q_v, v in V_bad; the Stage-2 input is the actual C3 source
pilot-region data.  IUT III, Remark 3.1.1, (ii): the completion degrees
[K_w:(F_mod)_v] are the normalization data.

COMPONENT, not a paper object.  Named future consumer: mainline Stage-2
model map fields M1/M2 of S3131Stage2ModelMapActual (same-C model map, IUT III
Definition 3.8(i) / Remark 3.1.1).  This file supplies the exact statements and
the actual prime-level part:

* qVFamTensorP_eq_base_val: the rational prime of the actual F-place over a bad
  place is the rational prime of the base bad place b.1 (actual, unconditional);
* S3131BadTensorIndexEquivalence: mainline's exact M1 proposition
  Nonempty (Bad (nativePlaceSelection T) ≃ C3.tensorIndex);
* S3131BadTensorPrimeMatch and S3131BadTensorPrimeMatch_of_basePlace: the
  prime-level index comparison, from the actual prime lemma and the same-C base
  place identification (mainline M0);
* S3131BadTensorPlaceMatch e placeTransport: the exact per-index tensorPlace
  match under the arithmetic-model place transport (M0);
* S3131BadTensorPrimeMatch_of_placeMatch: the per-index match implies the
  prime-level match.

The index equivalence itself is a pure comparison Prop and is NOT asserted.
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133S3131PlaceIndexComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The rational prime of the actual F-place over a bad place is the rational
prime of the base bad place: the actual unconditional prime comparison. -/
theorem qVFamTensorP_eq_base_val (b : Bad (nativePlaceSelection T)) :
    qVFamTensorP T b = (completionRationalPrime b.1).val := by
  unfold qVFamTensorP qVFamTensorPlace
  rw [← completionRationalPrime_comap (k := T.arithmetic.Fmod)
    ((nativeBadLift T).lift b)]
  rw [(nativeBadLift T).lift_comap b]

/-- The exact prime-level part of the badplace/tensor-index comparison: every
native bad place has the rational prime of the Stage-2 C3 place. -/
def S3131BadTensorPrimeMatch
    (T : SourceNativeInitialThetaData.{0} l)
    {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Prop :=
  ∀ b : Bad (nativePlaceSelection T), qVFamTensorP T b = C3.p

/-- The prime-level comparison follows from the base-place identification of the
same-C arithmetic model (mainline M0 supplies the base place equality). -/
theorem S3131BadTensorPrimeMatch_of_basePlace
    {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (hbase : ∀ b : Bad (nativePlaceSelection T),
      (completionRationalPrime b.1).val = C3.p) :
    S3131BadTensorPrimeMatch T C3 := by
  intro b
  rw [qVFamTensorP_eq_base_val T b, hbase b]

/-- Mainline's exact M1 proposition: a bijection between the native bad places
and the Stage-2 C3 tensor index.  Pure index/place comparison; not asserted. -/
def S3131BadTensorIndexEquivalence
    (T : SourceNativeInitialThetaData.{0} l)
    {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Prop :=
  Nonempty (Bad (nativePlaceSelection T) ≃ C3.tensorIndex)

/-- The exact per-index tensorPlace match under the arithmetic-model place
transport (mainline M0): the transport sends the actual F-place over b to the C3
tensorPlace at the index matched by e. -/
def S3131BadTensorPlaceMatch
    (T : SourceNativeInitialThetaData.{0} l)
    {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (placeTransport : NumberField.FinitePlace T.arithmetic.F ≃
      NumberField.FinitePlace I.initial.arithmetic.Fmod) : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    placeTransport (nativeBadToFPlace T b) =
      (C3.tensorPlaces (e b) (C3.tensorTuple (e b))).val

/-- The per-index tensorPlace match implies the prime-level comparison. -/
theorem S3131BadTensorPrimeMatch_of_placeMatch
    {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (placeTransport : NumberField.FinitePlace T.arithmetic.F ≃
      NumberField.FinitePlace I.initial.arithmetic.Fmod)
    (h : S3131BadTensorPlaceMatch T C3 e placeTransport)
    (hprimeTransport : ∀ b : Bad (nativePlaceSelection T),
      (completionRationalPrime (placeTransport (nativeBadToFPlace T b))).val =
        (completionRationalPrime (nativeBadToFPlace T b)).val) :
    S3131BadTensorPrimeMatch T C3 := by
  intro b
  have hb := h b
  have hprime : (completionRationalPrime
        (placeTransport (nativeBadToFPlace T b))).val =
      (completionRationalPrime
        ((C3.tensorPlaces (e b) (C3.tensorTuple (e b))).val)).val :=
    congrArg (fun v : NumberField.FinitePlace I.initial.arithmetic.Fmod =>
      (completionRationalPrime v).val) hb
  rw [show qVFamTensorP T b =
      (completionRationalPrime (nativeBadToFPlace T b)).val from rfl]
  rw [← hprimeTransport b, hprime]
  exact (C3.tensorPlaces (e b) (C3.tensorTuple (e b))).property

end LeanFormal.IUT.XiFPaper.S3133S3131PlaceIndexComparisonActual
