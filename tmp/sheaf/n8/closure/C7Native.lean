import tmp.sheaf.n8.closure.C7SourceU
import tmp.sheaf.n8.closure.C7HaarActual
import tmp.sheaf.n8.closure.C7Actual
import tmp.sheaf.n8.closure.C6ActualIQData
import Mathlib

/-!
# C7 native source-U to IQ closure

The paper hull is defined from the actual C4 region U through the actual
value-monoid source hull.  The IQ canonical hull is used only as containment
evidence: no equality between the source hull and the IQ hull is assumed.
The missing U -> IQ map is recorded as an exact donor declaration, not as an
axiom or a free equality.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7Native

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
open LeanFormal.IUT.N8Closure.C7SourceU
open LeanFormal.IUT.N8Closure.C7HaarActual
open LeanFormal.IUT.N8Closure.C7Actual

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
variable (n : ThetaPilotCarrier l)
variable (x : I.ThetaPilotPoint D.place.v)

/-- The paper hull H defined from the actual C4 region U, on the actual
value-monoid source carrier. -/
def sourcePaperHull : Set (I.ThetaPilotPoint D.place.v) :=
  I.sourceHolomorphicHull D.place.v D.place.R n

/-- The actual U is contained in the source paper hull. -/
theorem sourceU_subset_sourcePaperHull :
    sourceU (D := D) n x ⊆ sourcePaperHull (D := D) n :=
  sourceU_subset_sourceHolomorphicHull (D := D) n x

/-- Exact missing donor: an actual map from source points to the IQ carrier
that carries every point of U into the canonical IQ hull.  No equality of hulls
is asserted. -/
def SourceUToIQDonor : Prop :=
  ∃ toIQ : I.ThetaPilotPoint D.place.v →
      C6IQCarrier C3.tensorPlaces C3.tensorTuple,
    ∀ y ∈ sourceU (D := D) n x,
      toIQ y ∈ arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple

/-- Exact missing donor for the theta-image part: every T.thetaImage point lies
in the canonical IQ hull. -/
def ThetaImageContainmentDonor : Prop :=
  ∀ j : SignedLabel l.value,
    T.thetaImage n j ∈
      arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple

/-- Exact missing donor for the q-pilot/tensor-unit membership. -/
def QPilotHullMembershipDonor : Prop :=
  ABCBridge.N8.C7Actual.qPilotPoint (C3 := C3) ∈
    arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple

/-- The theta-image donor gives the C7 image-containment obligation for the
actual C6 data. -/
theorem permittedImage_subset_canonicalHull_of_thetaDonor
    (hTheta : ThetaImageContainmentDonor (C3 := C3) T n) :
    permittedImage (I := I) (C3 := C3) T n ⊆
      arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple := by
  rintro y ⟨j, rfl⟩
  exact hTheta j

/-- Native C7 closure: theta-image containment, q-pilot membership, and the
actual canonical-hull Haar positivity/finiteness give the C7 hull package.
Only the two actual donors are assumed; the paper hull H is not identified
with the canonical hull. -/
theorem sourceHolomorphicHullData_nonempty_of_native
    (hTheta : ThetaImageContainmentDonor (C3 := C3) T n)
    (hq : QPilotHullMembershipDonor (C3 := C3)) :
    Nonempty (SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := D) (C5 := C5) (mu := mu)
      (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu)
      (T := T) n) := by
  have hImage : permittedImage (I := I) (C3 := C3) T n ⊆
      commonHull (C3 := C3) mu (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu) := by
    rw [show commonHull (C3 := C3) mu
        (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu) =
        arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple by
      simp [commonHull, C6ActualIQData.actual]]
    exact permittedImage_subset_canonicalHull_of_thetaDonor (C3 := C3) (T := T) (n := n) hTheta
  have hq' : ABCBridge.N8.C7Actual.qPilotPoint (C3 := C3) ∈
      commonHull (C3 := C3) mu (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu) := by
    rw [show commonHull (C3 := C3) mu
        (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu) =
        arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple by
      simp [commonHull, C6ActualIQData.actual]]
    exact hq
  exact ⟨SourceHolomorphicHullData.ofObligations (C1 := C1) (C2 := C2)
    (C3 := C3) (D := D) (C5 := C5) (mu := mu)
    (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu) (T := T) (n := n)
    (actualC7Obligations (C3 := C3) (T := T) (n := n) (mu := mu) hImage hq')⟩

end LeanFormal.IUT.N8Closure.C7Native
