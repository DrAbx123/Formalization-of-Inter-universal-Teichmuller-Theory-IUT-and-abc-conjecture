import tmp.sheaf.n8.closure.SourceWitnessedOutput
import tmp.sheaf.n8.closure.SourceAlgorithmCompatibility
import tmp.sheaf.n8.closure.SourceThetaToIQ
import tmp.sheaf.n8.closure.C6ActualIQData
import Mathlib

/-!
# C7 stage 2: source holomorphic hull on the actual IQ carrier

This file uses the actual T11 SourceThetaToIQ image and q-pilot point, the
actual T9b C6ActualIQData hull/IQ interface, and the actual T2 C5 permitted
family. It does not use C6ProductVolumeData or a field-product proxy.

The former unconditional existence theorem was false for an arbitrary
C6ActualIQData value: its hull/interface fields are default-valued but may be
overridden independently.  This file now records the exact nonempty
obligations, constructs the hull package from them, and proves a concrete
counterexample to the old unconditional statement.  No sorry, axiom, or toy
carrier is used.
-/

noncomputable section

namespace ABCBridge.N8.C7Actual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open ABCBridge.N8.C4Actual
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceAlgorithmCompatibility
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8C6ActualIQ

universe ua uv upi umon ui uL uG

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {LAdd : Type uG} [AddGroup LAdd]
variable (C1 : SourceInputBinding I) (C2 : SourceLogKummerData I C1)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (D : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))
variable (C5 : SourceAlgorithmCompatibilityData I C1 C2 C3 D)
variable [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple))
variable [Measure.IsAddHaarMeasure mu]
variable (B : C6ActualIQData C3.tensorPlaces C3.tensorTuple mu)
variable (T : SourceThetaIQInterface (I := I) C3)

/-- The actual permitted image family in the C6 IQ carrier, from T11. -/
def permittedImage (n : ThetaPilotCarrier l) :
    Set (C6IQCarrier C3.tensorPlaces C3.tensorTuple) :=
  LeanFormal.IUT.N8Closure.SourceThetaToIQ.image (C3 := C3) T n

/-- The actual q-pilot point in the C6 IQ carrier, from T11. -/
def qPilotPoint :
    C6IQCarrier C3.tensorPlaces C3.tensorTuple :=
  LeanFormal.IUT.N8Closure.SourceThetaToIQ.qPilotPoint (C3 := C3)

/-- The common hull is the actual canonical hull carried by C6ActualIQData. -/
def commonHull (mu : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple))
    [Measure.IsAddHaarMeasure mu]
    (B : C6ActualIQData C3.tensorPlaces C3.tensorTuple mu) :
    Set (C6IQCarrier C3.tensorPlaces C3.tensorTuple) :=
  B.hull

/-- C7 output on the actual IQ carrier: the canonical hull contains the
permitted image family and the q-pilot point, and has finite positive
IQ-hull log-volume.

All properties are output proof fields, not input assumptions. -/
structure SourceHolomorphicHullData (T : SourceThetaIQInterface (I := I) C3)
    (n : ThetaPilotCarrier l) where
  /-- The IQ hull interface's hull is the C6ActualIQData hull. -/
  iqHull_eq : B.iqInterface.hull = commonHull (C3 := C3) mu B
  /-- The permitted image family is contained in the common hull. -/
  image_subset_hull : permittedImage (I := I) (C3 := C3) T n ⊆ commonHull (C3 := C3) mu B
  /-- Every permitted C5 label maps into the common hull. -/
  contains_permitted : ∀ c ∈ C5.permitted,
    T.thetaImage n c ∈ commonHull (C3 := C3) mu B
  /-- The actual canonical hull is contained in the lambda-scaled unit region. -/
  hull_subset_scaleShift : commonHull (C3 := C3) mu B ⊆
    B.iqInterface.scaleShift '' B.iqInterface.unitRegion
  /-- The IQ hull log-volume of the common hull is finite. -/
  logVolume_lt_top : B.iqInterface.logVolume (commonHull (C3 := C3) mu B) < ⊤
  /-- The Haar mass of the common hull is positive; signed log-volume may be negative. -/
  haar_pos : 0 < mu (commonHull (C3 := C3) mu B)
  /-- The Haar mass of the common hull is finite. -/
  haar_lt_top : mu (commonHull (C3 := C3) mu B) < ⊤
  /-- The actual q-pilot point belongs to the common hull. -/
  qPilot_mem : qPilotPoint (C3 := C3) ∈ commonHull (C3 := C3) mu B

/-- The exact nonempty obligations for the C7 hull package: the hull
interface identification, the T11 image containment, positive/finite Haar
mass, and q-pilot membership.  The remaining SourceHolomorphicHullData fields
are derived from B.iqInterface. -/
structure SourceHolomorphicHullObligations
    (T : SourceThetaIQInterface (I := I) C3) (n : ThetaPilotCarrier l) where
  iqHull_eq : B.iqInterface.hull = commonHull (C3 := C3) mu B
  image_subset_hull : permittedImage (I := I) (C3 := C3) T n ⊆
    commonHull (C3 := C3) mu B
  haar_pos : 0 < mu (commonHull (C3 := C3) mu B)
  haar_lt_top : mu (commonHull (C3 := C3) mu B) < ⊤
  qPilot_mem : qPilotPoint (C3 := C3) ∈ commonHull (C3 := C3) mu B

/-- Construct the C7 hull package from the exact obligations. -/
theorem SourceHolomorphicHullData.ofObligations
    (O : SourceHolomorphicHullObligations (C3 := C3) (mu := mu) (B := B) (T := T) (n := n)) :
    SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3) (D := D)
      (C5 := C5) (mu := mu) (B := B) (T := T) n := by
  refine
    { iqHull_eq := O.iqHull_eq
      image_subset_hull := O.image_subset_hull
      contains_permitted := ?_
      hull_subset_scaleShift := ?_
      logVolume_lt_top := ?_
      haar_pos := O.haar_pos
      haar_lt_top := O.haar_lt_top
      qPilot_mem := O.qPilot_mem }
  · intro c hc
    exact O.image_subset_hull ⟨c, rfl⟩
  · rw [← O.iqHull_eq]
    exact B.iqInterface.hull_subset_scaleShift
  · rw [← O.iqHull_eq]
    exact IQHullLogVolumeInterface.hull_logVolume_lt_top B.iqInterface

/-- Extract the exact obligations from a C7 hull package. -/
theorem obligationsOfHull
    (H : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := D) (C5 := C5) (mu := mu) (B := B) (T := T) n) :
    SourceHolomorphicHullObligations (C3 := C3) (mu := mu) (B := B) (T := T) n :=
  { iqHull_eq := H.iqHull_eq
    image_subset_hull := H.image_subset_hull
    haar_pos := H.haar_pos
    haar_lt_top := H.haar_lt_top
    qPilot_mem := H.qPilot_mem }

/-- Exact equivalence: a C7 hull package exists iff the explicit actual
obligations exist. -/
theorem sourceHolomorphicHullData_nonempty_iff_obligations
    (T : SourceThetaIQInterface (I := I) C3) (n : ThetaPilotCarrier l) :
    Nonempty (SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := D) (C5 := C5) (mu := mu) (B := B) (T := T) n) ↔
      Nonempty (SourceHolomorphicHullObligations (C3 := C3) (mu := mu) (B := B) (T := T) n) := by
  constructor
  · rintro ⟨H⟩
    exact ⟨obligationsOfHull (C1 := C1) (C2 := C2) (C3 := C3) (D := D)
      (C5 := C5) (mu := mu) (B := B) (T := T) (n := n) H⟩
  · rintro ⟨O⟩
    exact ⟨SourceHolomorphicHullData.ofObligations (C1 := C1) (C2 := C2)
      (C3 := C3) (D := D) (C5 := C5) (mu := mu) (B := B) (T := T) (n := n) O⟩

/-- The exact conditional existence theorem. -/
theorem sourceHolomorphicHullData_nonempty_of_obligations
    (T : SourceThetaIQInterface (I := I) C3) (n : ThetaPilotCarrier l)
    (O : SourceHolomorphicHullObligations (C3 := C3) (mu := mu) (B := B) (T := T) n) :
    Nonempty (SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := D) (C5 := C5) (mu := mu) (B := B) (T := T) n) :=
  ⟨SourceHolomorphicHullData.ofObligations (C1 := C1) (C2 := C2)
    (C3 := C3) (D := D) (C5 := C5) (mu := mu) (B := B) (T := T) (n := n) O⟩

/-- Concrete counterexample to the former unconditional theorem. -/
def emptyHullCounterexampleB :
    C6ActualIQData C3.tensorPlaces C3.tensorTuple mu where
  hull := ∅

theorem emptyHullCounterexampleB_iqHull_ne_empty :
    (emptyHullCounterexampleB (C3 := C3) (mu := mu)).iqInterface.hull ≠ ∅ := by
  have hpos := (measure_arithmeticTupleCanonicalRegions_pos_lt_top
    (places := C3.tensorPlaces) (tuple := C3.tensorTuple) mu).1.1
  rw [show (emptyHullCounterexampleB (C3 := C3) (mu := mu)).iqInterface.hull =
      arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple by
    simp [emptyHullCounterexampleB, arithmeticTupleIQHullLogVolumeInterface_hull]]
  intro h
  rw [h, measure_empty] at hpos
  exact lt_irrefl _ hpos

/-- The former unconditional sourceHolomorphicHullData_nonempty is false
for this actual C6ActualIQData value. -/
theorem not_sourceHolomorphicHullData_nonempty_emptyHull
    (T : SourceThetaIQInterface (I := I) C3) (n : ThetaPilotCarrier l) :
    ¬ Nonempty (SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := D) (C5 := C5) (mu := mu)
      (B := emptyHullCounterexampleB (C3 := C3) (mu := mu)) (T := T) n) := by
  rintro ⟨H⟩
  exact emptyHullCounterexampleB_iqHull_ne_empty (C3 := C3) (mu := mu)
    (by rw [H.iqHull_eq]; rfl)

end ABCBridge.N8.C7Actual

