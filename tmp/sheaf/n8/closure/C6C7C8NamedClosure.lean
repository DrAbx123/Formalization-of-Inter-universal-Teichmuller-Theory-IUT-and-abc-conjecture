import tmp.sheaf.n8.closure.C6ActualIdentification
import tmp.sheaf.n8.closure.C7HaarActual
import tmp.sheaf.n8.closure.C7UToIQProof
import tmp.sheaf.n8.closure.C8DegreeActual
import Mathlib

/-!
# C6/C7/C8 named closure (Wave1)

Consolidated exact closure for the actual C6 instance, the actual C7 hull from
the actual U-to-IQ map, and the actual C8 (Ob3-3) comparison.  The actual C6
instance and the C8 degree are reused, not redefined.  Named gaps remain only in
the upstream C7UToIQProof and C8DegreeActual files.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C6C7C8NamedClosure

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open ABCBridge.N8.C4Actual
open ABCBridge.N8.C7Actual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.N8C6.PaperNormalizedVolume
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceAlgorithmCompatibility
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8Closure.C7Actual
open LeanFormal.IUT.N8Closure.C7Native
open LeanFormal.IUT.N8Closure.C7UToIQProof
open LeanFormal.IUT.N8Closure.C8DegreeActual

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

/-- C6 actual closure: the actual instance satisfies the identification
predicate, reusing C6ActualIdentification. -/
theorem c6Actual_closure :
    (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).IsActual :=
  C6ActualIQData.actual_isActual C3.tensorPlaces C3.tensorTuple mu

end LeanFormal.IUT.N8Closure.C6C7C8NamedClosure
