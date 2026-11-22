import tmp.sheaf.n8.closure.SourceHolomorphicHull

/-!
# C7 actual closure: exact obligations and conditional hull data

This file isolates the exact actual facts needed to inhabit
SourceHolomorphicHullData on the real IQ carrier.  It constructs the hull data
from those obligations and proves that existence of the hull data is exactly
equivalent to the obligations.  No arbitrary hull or free hypothesis is used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7Actual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open ABCBridge.N8.C4Actual
open ABCBridge.N8.C7Actual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceAlgorithmCompatibility
open LeanFormal.IUT.N8Closure.SourceThetaToIQ

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

/-- Exact actual obligations needed for the C7 hull package. -/
structure C7ActualObligations (T : SourceThetaIQInterface (I := I) C3)
    (n : ThetaPilotCarrier l) where
  /-- The IQ interface hull is the C6 actual hull. -/
  iqHull_eq : B.iqInterface.hull = commonHull (C3 := C3) mu B
  /-- Every actual T.thetaImage point lies in the C6 canonical hull. -/
  thetaImage_subset_hull :
    permittedImage (I := I) (C3 := C3) T n ⊆ commonHull (C3 := C3) mu B
  /-- The actual q-pilot/tensor unit lies in the C6 canonical hull. -/
  qPilot_mem :
    ABCBridge.N8.C7Actual.qPilotPoint (C3 := C3) ∈ commonHull (C3 := C3) mu B
  /-- The canonical hull has positive Haar mass. -/
  haar_pos : 0 < mu (commonHull (C3 := C3) mu B)
  /-- The canonical hull has finite Haar mass. -/
  haar_lt_top : mu (commonHull (C3 := C3) mu B) < ⊤

/-- The actual q-pilot point is the actual C3 tensor unit. -/
theorem qPilotPoint_eq_tensorUnit :
    ABCBridge.N8.C7Actual.qPilotPoint (C3 := C3) =
      (C3.tensorUnit : C6IQCarrier C3.tensorPlaces C3.tensorTuple) :=
  LeanFormal.IUT.N8Closure.SourceThetaToIQ.qPilotPoint_eq_tensorUnit C3

/-- Construct the C7 hull package from the exact actual obligations. -/
def SourceHolomorphicHullData.ofObligations
    (O : C7ActualObligations (C3 := C3) (mu := mu) (B := B) (T := T) (n := n)) :
    SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3) (D := D)
      (C5 := C5) (mu := mu) (B := B) (T := T) n where
  iqHull_eq := O.iqHull_eq
  image_subset_hull := O.thetaImage_subset_hull
  contains_permitted := by
    intro c hc
    exact O.thetaImage_subset_hull ⟨c, rfl⟩
  hull_subset_scaleShift := by
    rw [← O.iqHull_eq]
    exact B.iqInterface.hull_subset_scaleShift
  logVolume_lt_top := by
    rw [← O.iqHull_eq]
    exact IQHullLogVolumeInterface.hull_logVolume_lt_top B.iqInterface
  haar_pos := O.haar_pos
  haar_lt_top := O.haar_lt_top
  qPilot_mem := O.qPilot_mem

/-- Extract the exact obligations from any C7 hull package. -/
def obligationsOfHull
    (H : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3) (D := D)
      (C5 := C5) (mu := mu) (B := B) (T := T) n) :
    C7ActualObligations (C3 := C3) (mu := mu) (B := B) (T := T) (n := n) where
  iqHull_eq := H.iqHull_eq
  thetaImage_subset_hull := H.image_subset_hull
  qPilot_mem := H.qPilot_mem
  haar_pos := H.haar_pos
  haar_lt_top := H.haar_lt_top

/-- Exact equivalence: the C7 hull package exists iff the explicit actual
obligations hold.  This is the no-go form: the current source data cannot
produce the package without these three actual containment/positivity fields
(and the interface-hull equality). -/
theorem sourceHolomorphicHullData_nonempty_iff_obligations
    (T : SourceThetaIQInterface (I := I) C3) (n : ThetaPilotCarrier l) :
    Nonempty (SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := D) (C5 := C5) (mu := mu) (B := B) (T := T) n) ↔
      Nonempty (C7ActualObligations (C3 := C3) (mu := mu) (B := B) (T := T) (n := n)) := by
  constructor
  · rintro ⟨H⟩
    exact ⟨obligationsOfHull (C1 := C1) (C2 := C2) (C3 := C3) (D := D)
      (C5 := C5) (mu := mu) (B := B) (T := T) (n := n) H⟩
  · rintro ⟨O⟩
    exact ⟨SourceHolomorphicHullData.ofObligations (C1 := C1) (C2 := C2)
      (C3 := C3) (D := D) (C5 := C5) (mu := mu) (B := B) (T := T) (n := n) O⟩

end LeanFormal.IUT.N8Closure.C7Actual
