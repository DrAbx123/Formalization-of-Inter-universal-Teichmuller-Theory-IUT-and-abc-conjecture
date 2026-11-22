/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.xif.paper.BaseQFamilyActual
import tmp.sheaf.xif.paper.BaseQLogVolumeActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.QPilotObjectActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.Mzk1ActualReadingTargetActual
import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import Mathlib.Tactic

/-! # Explicit base-change / q-pilot correspondence structures (NO inhabitant)

Exact missing source objects for R1, as type-correct data structures only:

* `BaseChangePlaceCompletionCorrespondence`: F-place (`qVFamTensorPlace`, F-side) vs
  K-place (`nativeBaseSectionPlace`, K-side) — different fields, so this is an explicit
  correspondence structure (both comap to b.1) with a completion comparison map and its
  explicit norm data; no equality of places is asserted (type-incorrect).
* `BaseChangeQElementCorrespondence`: the Tate parameters correspond under the completion
  map: `completionMap (qVFamily q) = nativeBaseQFamily q` (after casts along the place
  correspondences); no element equality across F/K carriers is claimed.
* `QPilotC3SignedAggregation`: single C3 q-pilot signed log equals the global weighted sum
  `-M` (or collapses to the single Bad place); this is the single-place-vs-global-sum datum.

No inhabitant, no axiom/sorry; consumers may only use these as explicit hypotheses. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1BaseChangeQCorrespondenceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.Mzk1ActualReadingTargetActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual

universe u v

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- **Explicit F/K place + completion correspondence** at a native bad place.
Type-incorrect to demand place equality (F vs K); this structure records the real datum. -/
structure BaseChangePlaceCompletionCorrespondence
    (b : Bad (nativePlaceSelection T)) where
  fPlace : NumberField.FinitePlace T.arithmetic.F
  kPlace : NumberField.FinitePlace T.arithmetic.K
  fPlace_comap_F : fPlace = NumberFieldFinitePlace.comap (k := T.arithmetic.F) kPlace
  fPlace_lift : fPlace = (nativeBadLift T).lift b
  kPlace_eq : kPlace = nativeBaseSectionPlace T b
  fPlace_comap : NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) fPlace = b.1
  kPlace_comap : NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) kPlace = b.1
  completionMap : Completion fPlace → Completion kPlace
  n : Nat
  n_pos : 0 < n
  completionMap_norm : ∀ x : Completion fPlace, ‖completionMap x‖ = ‖x‖ ^ n

/-- The canonical F-place lift obtained by contracting the actual K-section lift:
`comap_F (nativeBaseSectionPlace T b)`.  Unlike `nativeBadLift.lift b` (chosen by
`Classical.choose` from `comap_surjective`), this lift is DEFINED by contraction, so
`comap_F (nativeBaseSectionPlace T b) = nativeBaseContractionFPlace T b` is rfl. -/
noncomputable def nativeBaseContractionFPlace
    (b : Bad (nativePlaceSelection T)) : NumberField.FinitePlace T.arithmetic.F :=
  NumberFieldFinitePlace.comap (k := T.arithmetic.F) (nativeBaseSectionPlace T b)

/-- The contraction lift really lies above the bad moduli place. -/
theorem nativeBaseContractionFPlace_comap
    (b : Bad (nativePlaceSelection T)) :
    NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod)
      (nativeBaseContractionFPlace T b) = b.1 := by
  unfold nativeBaseContractionFPlace
  rw [NumberFieldFinitePlace.comap_comap]
  exact nativeBaseSectionPlace_comap T b

/-- **The exact alignment missing for `nativeBadLift`**: the chosen lying-over F-lift
agrees with the canonical contraction of the K-section lift.  This is (a); it is NOT
provable as-is because `nativeBadLift` uses `Classical.choose` from `comap_surjective`
while the right-hand side is defined by contraction. -/
def NativeBadLiftAlignment (b : Bad (nativePlaceSelection T)) : Prop :=
  nativeBaseContractionFPlace T b = (nativeBadLift T).lift b

/-- **Construct the place/completion correspondence from the actual base-change map.**
Only the F-place lift coherence (a) is required as an explicit hypothesis:
`comap_F (nativeBaseSectionPlace T b) = (nativeBadLift T).lift b`.
The completion map is the green `NumberFieldFinitePlace.completionMap`; its norm power
formula `‖completionMap x‖ = ‖x‖ ^ relativeCompletionDegree` is green
(`norm_completionMap_pow`). -/
noncomputable def baseChangePlaceCompletionCorrespondence
    (b : Bad (nativePlaceSelection T))
    (hplace : NumberFieldFinitePlace.comap (k := T.arithmetic.F)
      (nativeBaseSectionPlace T b) = (nativeBadLift T).lift b) :
    BaseChangePlaceCompletionCorrespondence T b where
  fPlace := NumberFieldFinitePlace.comap (k := T.arithmetic.F) (nativeBaseSectionPlace T b)
  kPlace := nativeBaseSectionPlace T b
  fPlace_comap_F := rfl
  fPlace_lift := hplace
  kPlace_eq := rfl
  fPlace_comap := by
    show NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod)
      (NumberFieldFinitePlace.comap (k := T.arithmetic.F) (nativeBaseSectionPlace T b)) = b.1
    rw [NumberFieldFinitePlace.comap_comap]
    exact nativeBaseSectionPlace_comap T b
  kPlace_comap := nativeBaseSectionPlace_comap T b
  completionMap := NumberFieldFinitePlace.completionMap (k := T.arithmetic.F)
    (K := T.arithmetic.K) (nativeBaseSectionPlace T b)
  n := relativeCompletionDegree (k := T.arithmetic.F) (nativeBaseSectionPlace T b)
  n_pos := relativeCompletionDegree_pos (k := T.arithmetic.F) (nativeBaseSectionPlace T b)
  completionMap_norm := fun x => by
    by_cases hx : x = 0
    · subst hx
      rw [map_zero, norm_zero]
      have hn : relativeCompletionDegree (k := T.arithmetic.F)
          (nativeBaseSectionPlace T b) ≠ 0 :=
        (relativeCompletionDegree_pos (k := T.arithmetic.F)
          (nativeBaseSectionPlace T b)).ne'
      simp [hn]
    · exact norm_completionMap_pow (k := T.arithmetic.F) (K := T.arithmetic.K)
        (nativeBaseSectionPlace T b) x hx

/-- **Explicit Tate-parameter element correspondence** under the completion map. -/
structure BaseChangeQElementCorrespondence
    {b : Bad (nativePlaceSelection T)}
    (bc : BaseChangePlaceCompletionCorrespondence T b) where
  q_eq :
    bc.completionMap (bc.fPlace_lift.symm ▸ (qVFamily T b).q) =
      bc.kPlace_eq.symm ▸ (nativeBaseQFamily T b).q

/-- **Single C3 vs global Bad sum**: the C3 signed readout equals the global weighted
normalized signed sum (or collapses to one Bad place).  This is source data, no inhabitant. -/
structure QPilotC3SignedAggregation
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    {V : Type} (I : OriginalInput l V)
    (P : PaperQPilotObjectActual I) where
  signed_eq_global : P.signedQPilotLogVolume = -nativeGlobalQPilotNormalizedLogMagnitude T

/-- **Conditional R1 from the explicit structures**: if the same-q norm identification
holds (qVFam default norm = baseQ norm) and the C3 signed readout aggregates to `-M`,
then the original q reading is at most the normalized signed q scalar. -/
theorem qPilotLogVolumeReading_le_actualQPilotSignedLogClassical_of_structures
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    {V : Type} (I : OriginalInput l V)
    (P : PaperQPilotObjectActual I)
    (hq : ∀ b : Bad (nativePlaceSelection T),
      qVFamDefaultNorm T b = ‖(baseQ T b).q‖)
    (agg : QPilotC3SignedAggregation T I P) :
    qPilotLogVolumeReading P ≤ actualQPilotSignedLogClassical T := by
  have hAM : actualQPilotMagnitudeClassical T ≤
      nativeGlobalQPilotNormalizedLogMagnitude T :=
    actualQPilotMagnitudeClassical_le_nativeGlobal_of_same_q T hq
  calc qPilotLogVolumeReading P = P.signedQPilotLogVolume := rfl
    _ = -nativeGlobalQPilotNormalizedLogMagnitude T := agg.signed_eq_global
    _ ≤ -actualQPilotMagnitudeClassical T := by linarith
    _ = actualQPilotSignedLogClassical T := rfl

def correspondenceRows : List (String × String × String) :=
  [ ("BaseChangePlaceCompletionCorrespondence", "F-place vs K-place correspondence + completion map/norm data (no place equality)", "EXPLICIT DATA, NO INHABITANT"),
    ("nativeBaseContractionFPlace", "canonical F-lift = comap_F (K-section lift); comap to b.1 green", "DEFINED + PROVED"),
    ("NativeBadLiftAlignment", "comap_F (nativeBaseSectionPlace) = (nativeBadLift).lift b", "EXACT GAP (a)"),
    ("baseChangePlaceCompletionCorrespondence", "constructed from hplace + green completionMap/norm power (only (a) needed)", "CONSTRUCTED (given fPlace_lift coherence)"),
    ("BaseChangeQElementCorrespondence", "completionMap(qVFamily q) = nativeBaseQFamily q (after casts)", "EXPLICIT DATA, NO INHABITANT"),
    ("QPilotC3SignedAggregation", "single C3 signed log = -M global weighted sum", "EXPLICIT DATA, NO INHABITANT"),
    ("qPilotLogVolumeReading_le_actualQPilotSignedLogClassical_of_structures", "same-q norm id + aggregation => R1", "PROVED (conditional)") ]

theorem correspondenceRows_length : correspondenceRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1BaseChangeQCorrespondenceActual

end