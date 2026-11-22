import tmp.sheaf.n8.closure.C7Actual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# C7 actual hull data from the C3/C6 source block

Task-516 bottom-up derivation attempt.

Inputs:
* C7Actual.lean: SourceHolomorphicHullData.ofObligations and
  C7ActualObligations;
* SourceHolomorphicHull.lean: the actual hull package and its obligations;
* SourceDegreeHullC3.lean: the C3 tensor-block consumer.

Concrete C6 choice: the actual canonical IQ data
C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu.

Derived from the source/C6 data:
* iqHull_eq for the actual canonical hull;
* positive and finite Haar mass of the actual canonical hull;
* consequently every SourceHolomorphicHullData field except the two
  containment/membership obligations is derived.

Exact remaining source fields (primitive, not derived):
1. thetaImage_subset_hull: the T11 permitted theta image
   permittedImage T n is contained in the actual canonical hull.
   The current tree has no theorem relating the arbitrary T.thetaCompletion
   or thetaIQInterfaceOfQUnit to the canonical hull.
2. qPilot_mem: the actual q-pilot point (the C3 tensor unit) lies in the
   actual canonical hull. The canonical hull is the arithmetic-tuple canonical
   hull; C3.tensorUnit is an actual unit of the tensor block, but no source
   theorem places it in the canonical hull.

These two fields are kept explicit in C3ConcreteHullObligations. No arbitrary
data, placeholder proposition, trivial unit, fake proof, or uninterpreted declaration is used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7FromSource

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open ABCBridge.N8.C4Actual
open ABCBridge.N8.C7Actual
open LeanFormal.IUT.N8Closure.C7Actual
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
variable (T : SourceThetaIQInterface (I := I) C3)

/-- The actual C6 canonical IQ data on the C3 tensor block. -/
abbrev actualB : C6ActualIQData C3.tensorPlaces C3.tensorTuple mu :=
  C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu

/-- The actual canonical hull of the C6 data. -/
abbrev actualCommonHull : Set (C6IQCarrier C3.tensorPlaces C3.tensorTuple) :=
  ABCBridge.N8.C7Actual.commonHull (C3 := C3) mu (actualB (C3 := C3) (mu := mu))

/-- The actual IQ interface hull of the C6 data is the actual common hull. -/
theorem actual_iqHull_eq :
    (actualB (C3 := C3) (mu := mu)).iqInterface.hull =
      actualCommonHull (C3 := C3) (mu := mu) := by
  simp [actualB, actualCommonHull, C6ActualIQData.actual,
    ABCBridge.N8.C7Actual.commonHull,
    arithmeticTupleIQHullLogVolumeInterface_hull]

/-- The actual canonical hull has positive Haar mass. -/
theorem actual_haar_pos :
    0 < mu (actualCommonHull (C3 := C3) (mu := mu)) := by
  have h := measure_arithmeticTupleCanonicalRegions_pos_lt_top
    (places := C3.tensorPlaces) (tuple := C3.tensorTuple) mu
  simpa [actualCommonHull, actualB, C6ActualIQData.actual,
    ABCBridge.N8.C7Actual.commonHull] using h.1.1

/-- The actual canonical hull has finite Haar mass. -/
theorem actual_haar_lt_top :
    mu (actualCommonHull (C3 := C3) (mu := mu)) < ⊤ := by
  have h := measure_arithmeticTupleCanonicalRegions_pos_lt_top
    (places := C3.tensorPlaces) (tuple := C3.tensorTuple) mu
  simpa [actualCommonHull, actualB, C6ActualIQData.actual,
    ABCBridge.N8.C7Actual.commonHull] using h.1.2

/-- Exact primitive containment fields for the C3 block. -/
structure C3ConcreteHullObligations
    (T : SourceThetaIQInterface (I := I) C3) (n : ThetaPilotCarrier l) where
  /-- The actual T11 theta image lies in the actual canonical hull. -/
  thetaImage_subset_hull :
    ABCBridge.N8.C7Actual.permittedImage (I := I) (C3 := C3) T n ⊆
      actualCommonHull (C3 := C3) (mu := mu)
  /-- The actual q-pilot/tensor unit lies in the actual canonical hull. -/
  qPilot_mem :
    ABCBridge.N8.C7Actual.qPilotPoint (C3 := C3) ∈
      actualCommonHull (C3 := C3) (mu := mu)

/-- The concrete primitive fields plus the source/C6-derived facts give the
C7 actual obligations for the C3 block. -/
theorem C3ConcreteHullObligations.toC7ActualObligations
    {T : SourceThetaIQInterface (I := I) C3} {n : ThetaPilotCarrier l}
    (O : C3ConcreteHullObligations (C3 := C3) (mu := mu) T n) :
    C7ActualObligations (B := actualB (C3 := C3) (mu := mu)) (T := T) (n := n) where
  iqHull_eq := actual_iqHull_eq (C3 := C3) (mu := mu)
  thetaImage_subset_hull := O.thetaImage_subset_hull
  qPilot_mem := O.qPilot_mem
  haar_pos := actual_haar_pos (C3 := C3) (mu := mu)
  haar_lt_top := actual_haar_lt_top (C3 := C3) (mu := mu)

/-- Concrete hull data from the exact primitive containment fields. -/
theorem concreteSourceHolomorphicHullData
    {T : SourceThetaIQInterface (I := I) C3} {n : ThetaPilotCarrier l}
    (O : C3ConcreteHullObligations (C3 := C3) (mu := mu) T n) :
    SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3) (D := D)
      (C5 := C5) (mu := mu) (B := actualB (C3 := C3) (mu := mu)) (T := T) n :=
  SourceHolomorphicHullData.ofObligations (C1 := C1) (C2 := C2) (C3 := C3)
    (D := D) (C5 := C5) (mu := mu) (B := actualB (C3 := C3) (mu := mu))
    (T := T) (n := n) O.toC7ActualObligations

/-- Extraction of the exact primitive fields from a concrete hull package. -/
theorem concreteObligationsOfHull
    {T : SourceThetaIQInterface (I := I) C3} {n : ThetaPilotCarrier l}
    (H : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3) (D := D)
      (C5 := C5) (mu := mu) (B := actualB (C3 := C3) (mu := mu)) (T := T) n) :
    C3ConcreteHullObligations (C3 := C3) (mu := mu) T n where
  thetaImage_subset_hull := H.image_subset_hull
  qPilot_mem := H.qPilot_mem

/-- Exact equivalence: on the actual canonical C6 hull, a C7 hull package
exists iff the two primitive containment fields exist. -/
theorem concreteSourceHolomorphicHullData_nonempty_iff
    (T : SourceThetaIQInterface (I := I) C3) (n : ThetaPilotCarrier l) :
    Nonempty (SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := D) (C5 := C5) (mu := mu)
      (B := actualB (C3 := C3) (mu := mu)) (T := T) n) ↔
      Nonempty (C3ConcreteHullObligations (C3 := C3) (mu := mu) T n) := by
  constructor
  · rintro ⟨H⟩
    exact ⟨concreteObligationsOfHull (C1 := C1) (C2 := C2) (C3 := C3)
      (D := D) (C5 := C5) (mu := mu) H⟩
  · rintro ⟨O⟩
    exact ⟨concreteSourceHolomorphicHullData (C1 := C1) (C2 := C2)
      (C3 := C3) (D := D) (C5 := C5) (mu := mu) O⟩

/-- The actual C3 tensor unit is the q-pilot point. -/
theorem c3_qPilot_eq_tensorUnit :
    ABCBridge.N8.C7Actual.qPilotPoint (C3 := C3) =
      (C3.tensorUnit : C6IQCarrier C3.tensorPlaces C3.tensorTuple) :=
  LeanFormal.IUT.N8Closure.SourceThetaToIQ.qPilotPoint_eq_tensorUnit (I := I) C3


end LeanFormal.IUT.N8Closure.C7FromSource

end
