import tmp.sheaf.n8.closure.C7ContainmentActual
import tmp.sheaf.n8.closure.C7ActualFromSource

/-! # Native C7 membership proof attempt (write-only)

Task-525 deep attempt.  The target memberships are

    (C3.tensorUnit : C6IQCarrier C3.tensorPlaces C3.tensorTuple)
      ∈ actualCommonHull
    permittedImage (I := I) (C3 := C3) T n ⊆ actualCommonHull.

## What is proved

* `qPilotPoint = C3.tensorUnit` (actual C3/T11 equality).
* `permittedImage T n` is exactly the set of actual theta images
  `T.thetaImage n j = C3.tensorLanding (T.thetaCompletion n j)`.
* The two target memberships are equivalent to the pointwise primitive
  membership pair below.
* The primitive pair constructs the C7 hull package through the existing
  `C3ConcreteHullObligations`/`SourceHolomorphicHullData.ofObligations`
  constructor.

## Exact missing theorem/primitive

No existing source theorem proves either membership.  The canonical hull is
the arithmetic-tuple canonical hull (a decomposition-independent bounded
hull), while `C3.tensorUnit` is an arbitrary unit carried by the C3 block;
`C3.tensorLanding_q` identifies only the q landing `tensorLanding q =
tensorUnit`, not a hull membership.  Likewise `T.thetaImage n j =
C3.tensorLanding (T.thetaCompletion n j)` is only a definitional transport,
not a canonical-hull membership.  The missing relation is the exact
`NativeC7MembershipPrimitive` structure below.

No arbitrary data, fake membership, `True`, `PUnit`, or axiom is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.N8Closure.C7FromSource.NativeMembership

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
open LeanFormal.IUT.N8Closure.C7FromSource.Containment

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
theorem qPilotPoint_eq_tensorUnit :
    ABCBridge.N8.C7Actual.qPilotPoint (C3 := C3) =
      (C3.tensorUnit : C6IQCarrier C3.tensorPlaces C3.tensorTuple) :=
  c3_qPilot_eq_tensorUnit (C3 := C3)

/-- The q-pilot membership is exactly tensor-unit membership in the actual
common hull. -/
theorem qPilot_mem_iff_tensorUnit_mem :
    ABCBridge.N8.C7Actual.qPilotPoint (C3 := C3) ∈
        actualCommonHull (C3 := C3) (mu := mu) ↔
      (C3.tensorUnit : C6IQCarrier C3.tensorPlaces C3.tensorTuple) ∈
        actualCommonHull (C3 := C3) (mu := mu) := by
  rw [qPilotPoint_eq_tensorUnit]

/-- The permitted image is exactly the actual theta image family. -/
theorem permittedImage_eq_image (n : ThetaPilotCarrier l) :
    permittedImage (I := I) (C3 := C3) T n =
      image (I := I) C3 T n := rfl

/-- A theta image is in the actual hull iff its actual tensor landing is. -/
theorem thetaImage_mem_iff_tensorLanding_mem
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    T.thetaImage n j ∈ actualCommonHull (C3 := C3) (mu := mu) ↔
      C3.tensorLanding (T.thetaCompletion n j) ∈
        actualCommonHull (C3 := C3) (mu := mu) := by
  rw [T.thetaImage_eq n j]

/-- Pointwise theta-image membership is exactly containment of the permitted
image. -/
theorem permittedImage_subset_iff_forall_mem
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

/-- Exact primitive membership pair for the C7 target. -/
structure NativeC7MembershipPrimitive (n : ThetaPilotCarrier l) where
  tensorUnit_mem :
    (C3.tensorUnit : C6IQCarrier C3.tensorPlaces C3.tensorTuple) ∈
      actualCommonHull (C3 := C3) (mu := mu)
  thetaImage_subset :
    permittedImage (I := I) (C3 := C3) T n ⊆
      actualCommonHull (C3 := C3) (mu := mu)

/-- The primitive pair yields the q-pilot membership directly. -/
theorem qPilot_mem_of_primitive {n : ThetaPilotCarrier l}
    (P : NativeC7MembershipPrimitive (C3 := C3) (mu := mu) T n) :
    ABCBridge.N8.C7Actual.qPilotPoint (C3 := C3) ∈
      actualCommonHull (C3 := C3) (mu := mu) :=
  (qPilot_mem_iff_tensorUnit_mem (C3 := C3) (mu := mu)).mpr P.tensorUnit_mem

/-- The primitive pair is definitionally the concrete C3 containment
obligations (after converting q-pilot membership back to tensor-unit
membership). -/
def NativeC7MembershipPrimitive.toConcrete {n : ThetaPilotCarrier l}
    (P : NativeC7MembershipPrimitive (C3 := C3) (mu := mu) T n) :
    C3ConcreteHullObligations (C3 := C3) (mu := mu) T n where
  thetaImage_subset_hull := P.thetaImage_subset
  qPilot_mem := qPilot_mem_of_primitive (C3 := C3) (mu := mu) P

/-- The concrete C3 obligations give the primitive pair. -/
def C3ConcreteHullObligations.toNativePrimitive {n : ThetaPilotCarrier l}
    (O : C3ConcreteHullObligations (C3 := C3) (mu := mu) T n) :
    NativeC7MembershipPrimitive (C3 := C3) (mu := mu) T n where
  tensorUnit_mem :=
    (qPilot_mem_iff_tensorUnit_mem (C3 := C3) (mu := mu)).mp O.qPilot_mem
  thetaImage_subset := O.thetaImage_subset_hull

/-- The C7 hull package exists exactly from the native primitive pair. -/
theorem concreteSourceHolomorphicHullData_of_nativePrimitive
    {n : ThetaPilotCarrier l}
    (P : NativeC7MembershipPrimitive (C3 := C3) (mu := mu) T n) :
    Nonempty (SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := D) (C5 := C5) (mu := mu)
      (B := actualB (C3 := C3) (mu := mu)) (T := T) n) :=
  concreteSourceHolomorphicHullData_of_primitives (C1 := C1) (C2 := C2)
    (C3 := C3) (D := D) (C5 := C5) (mu := mu) P.toConcrete

/-- Exact primitive proposition: the two native memberships. -/
def NativeC7MembershipRequired (n : ThetaPilotCarrier l) : Prop :=
  Nonempty (NativeC7MembershipPrimitive (C3 := C3) (mu := mu) T n)

end LeanFormal.IUT.N8Closure.C7FromSource.NativeMembership

end
