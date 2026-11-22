import tmp.sheaf.n8.closure.C7ActualFromSource

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# C7 containment attempt from actual C3/C6/source data

Task-518 write-only attempt.

Inputs:
* tmp/sheaf/n8/closure/C7ActualFromSource.lean:
  actualB, actualCommonHull, C3ConcreteHullObligations, actual_iqHull_eq,
  actual_haar_pos, actual_haar_lt_top, concreteSourceHolomorphicHullData;
* SourceThetaToIQ.lean: permittedImage/image, qPilotPoint, thetaImage_eq,
  qPilotPoint_eq_tensorUnit;
* SourcePilotRegion.lean: C3.tensorUnit, tensorLanding, tensorLanding_q.

Derivation attempt result:
The actual q-pilot point is exactly the C3 tensor unit, and the theta image is
exactly the finite set of C3 tensor landings. The two required C7 containment
fields are therefore equivalent to:

1. tensorUnit in the actual canonical hull;
2. every thetaImage T n j in the actual canonical hull.

No theorem in the current source tree places the arbitrary C3 tensorUnit or
the arbitrary C3.tensorLanding images in the arithmetic-tuple canonical hull.
tensorLanding_q identifies only the q landing, not a hull membership, and
thetaImage_eq identifies only the tensor-landing form, not a hull membership.
These two memberships are therefore exact primitive source fields.

No arbitrary data, placeholder proposition, trivial unit, fake proof, or
uninterpreted declaration is used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7FromSource.Containment

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
open LeanFormal.IUT.N8Closure.C7FromSource

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

/-- The actual q-pilot point is the C3 tensor unit. -/
theorem qPilot_eq_tensorUnit :
    ABCBridge.N8.C7Actual.qPilotPoint (C3 := C3) =
      (C3.tensorUnit : C6IQCarrier C3.tensorPlaces C3.tensorTuple) :=
  c3_qPilot_eq_tensorUnit (C3 := C3)

/-- The q-pilot membership primitive is exactly the tensor-unit membership
condition. This is a genuine equivalence, not a proof of either side. -/
theorem qPilot_mem_iff_tensorUnit_mem :
    ABCBridge.N8.C7Actual.qPilotPoint (C3 := C3) ∈
        actualCommonHull (C3 := C3) (mu := mu) ↔
      (C3.tensorUnit : C6IQCarrier C3.tensorPlaces C3.tensorTuple) ∈
        actualCommonHull (C3 := C3) (mu := mu) := by
  rw [qPilot_eq_tensorUnit]

/-- A theta-image point is in the actual hull iff its C3 tensor landing is in
the actual hull. This reduces the image containment primitive to the pointwise
membership of the actual thetaImage values. -/
theorem thetaImage_mem_iff_tensorLanding_mem
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    T.thetaImage n j ∈ actualCommonHull (C3 := C3) (mu := mu) ↔
      C3.tensorLanding (T.thetaCompletion n j) ∈
        actualCommonHull (C3 := C3) (mu := mu) := by
  rw [T.thetaImage_eq n j]

/-- The subset containment primitive is equivalent to pointwise membership of
the actual theta images. -/
theorem thetaImage_subset_hull_iff_forall_mem
    (n : ThetaPilotCarrier l) :
    permittedImage (I := I) (C3 := C3) T n ⊆
        actualCommonHull (C3 := C3) (mu := mu) ↔
      ∀ j : SignedLabel l.value,
        T.thetaImage n j ∈ actualCommonHull (C3 := C3) (mu := mu) := by
  constructor
  · intro h j
    exact h ⟨j, rfl⟩
  · rintro h x ⟨j, rfl⟩
    exact h j

/-- A pointwise theta-image membership family gives the C7 image containment
field. -/
theorem thetaImage_subset_hull_of_forall
    (n : ThetaPilotCarrier l)
    (h : ∀ j : SignedLabel l.value,
      T.thetaImage n j ∈ actualCommonHull (C3 := C3) (mu := mu)) :
    permittedImage (I := I) (C3 := C3) T n ⊆
      actualCommonHull (C3 := C3) (mu := mu) :=
  (thetaImage_subset_hull_iff_forall_mem (C3 := C3) (mu := mu) T n).mpr h

/-- A tensor-unit membership gives the C7 q-pilot membership field. -/
theorem qPilot_mem_of_tensorUnit_mem
    (h : (C3.tensorUnit : C6IQCarrier C3.tensorPlaces C3.tensorTuple) ∈
      actualCommonHull (C3 := C3) (mu := mu)) :
    ABCBridge.N8.C7Actual.qPilotPoint (C3 := C3) ∈
      actualCommonHull (C3 := C3) (mu := mu) :=
  (qPilot_mem_iff_tensorUnit_mem (C3 := C3) (mu := mu)).mpr h

/-- The exact two primitive fields of the C3 containment obligations. This is
the same pair as C3ConcreteHullObligations, restated for the derivation
attempt; it is not a new assumption. -/
structure C3ContainmentPrimitives
    (T : SourceThetaIQInterface (I := I) C3) (n : ThetaPilotCarrier l) where
  thetaImage_subset_hull :
    permittedImage (I := I) (C3 := C3) T n ⊆
      actualCommonHull (C3 := C3) (mu := mu)
  qPilot_mem :
    ABCBridge.N8.C7Actual.qPilotPoint (C3 := C3) ∈
      actualCommonHull (C3 := C3) (mu := mu)

/-- The primitive pair is definitionally the concrete C7 obligations. -/
def C3ContainmentPrimitives.toConcrete
    {T : SourceThetaIQInterface (I := I) C3} {n : ThetaPilotCarrier l}
    (P : C3ContainmentPrimitives (C3 := C3) (mu := mu) T n) :
    C3ConcreteHullObligations (C3 := C3) (mu := mu) T n where
  thetaImage_subset_hull := P.thetaImage_subset_hull
  qPilot_mem := P.qPilot_mem

/-- Conversely, concrete C7 obligations give the primitive pair. -/
def C3ConcreteHullObligations.toPrimitives
    {T : SourceThetaIQInterface (I := I) C3} {n : ThetaPilotCarrier l}
    (O : C3ConcreteHullObligations (C3 := C3) (mu := mu) T n) :
    C3ContainmentPrimitives (C3 := C3) (mu := mu) T n where
  thetaImage_subset_hull := O.thetaImage_subset_hull
  qPilot_mem := O.qPilot_mem

/-- The primitive pair yields the C7 hull package through the existing
obligation constructor. -/
theorem concreteSourceHolomorphicHullData_of_primitives
    {T : SourceThetaIQInterface (I := I) C3} {n : ThetaPilotCarrier l}
    (P : C3ContainmentPrimitives (C3 := C3) (mu := mu) T n) :
    Nonempty (SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := D) (C5 := C5) (mu := mu)
      (B := actualB (C3 := C3) (mu := mu)) (T := T) n) :=
  ⟨concreteSourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
    (D := D) (C5 := C5) (mu := mu) P.toConcrete⟩

/-- Exact nonempty equivalence for the primitive pair. -/
theorem concreteSourceHolomorphicHullData_nonempty_iff_primitives
    (T : SourceThetaIQInterface (I := I) C3) (n : ThetaPilotCarrier l) :
    Nonempty (SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := D) (C5 := C5) (mu := mu)
      (B := actualB (C3 := C3) (mu := mu)) (T := T) n) ↔
      Nonempty (C3ContainmentPrimitives (C3 := C3) (mu := mu) T n) := by
  constructor
  · rintro ⟨H⟩
    exact ⟨(concreteObligationsOfHull (C1 := C1) (C2 := C2) (C3 := C3)
      (D := D) (C5 := C5) (mu := mu) H).thetaImage_subset_hull,
      (concreteObligationsOfHull (C1 := C1) (C2 := C2) (C3 := C3)
      (D := D) (C5 := C5) (mu := mu) H).qPilot_mem⟩
  · rintro ⟨P⟩
    exact concreteSourceHolomorphicHullData_of_primitives (C1 := C1) (C2 := C2)
      (C3 := C3) (D := D) (C5 := C5) (mu := mu) P


end LeanFormal.IUT.N8Closure.C7FromSource.Containment

end
