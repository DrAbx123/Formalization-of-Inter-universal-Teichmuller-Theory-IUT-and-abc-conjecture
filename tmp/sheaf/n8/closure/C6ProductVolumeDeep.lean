import tmp.sheaf.n8.closure.C7Interface
import tmp.sheaf.n8.closure.SourceWitnessedOutput
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import Mathlib

/-! # Deep C6ProductVolumeData construction at ThetaPilotPoint

The actual C3 tensor block is the finite product of common prime completions

  (i : iota) -> CommonPrimeCompletion (places i (tuple i)).

Each CommonPrimeCompletion is a proper normed local field.  The C7 interface
C6ProductVolumeData at Y = I.ThetaPilotPoint D.place.v therefore needs:

* the finite C3 index iota;
* the actual common-prime-completion family K i;
* a measurable space on the product;
* a carrier equivalence ThetaPilotPoint ≃ ((i : iota) -> K i);
* a product Haar measure mu;
* finite-measure-on-compacts and open-positive instances.

This file constructs the C6ProductVolumeData from exactly such data.  The
finite index and the proper normed local-field family are actual C3 data; the
carrier equivalence and the product measure/instances are the missing
primitives and remain fields.  No arbitrary index, field family, equivalence
or measure is chosen.

No True/PUnit/axiom/sorry. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.N8Closure.C6ProductVolumeDeep

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C7Actual
open ABCBridge.N8.C4Actual
open MeasureTheory

universe ua uv upi umon ui uL uY uK uIot uVp

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} [Group Label]
variable {D : SourceWitnessedOutputData I Label}

variable {K0 : Type uK} [Field K0] [NumberField K0] {p : Nat} [Fact p.Prime]
variable {iota : Type uIot} [Fintype iota] {Vp : iota → Type uVp}
variable (places : (i : iota) → Vp i → FinitePlaceAtPrime K0 p)
variable (tuple : (i : iota) → Vp i)

/-- The actual product index of the C3 tensor block. -/
abbrev C6TensorIndex : Type uIot := iota

/-- The actual proper normed local field at a product index. -/
abbrev C6TensorLocalField (i : iota) : Type uK :=
  CommonPrimeCompletion (places i (tuple i))

/-- The actual ThetaPilotPoint carrier. -/
abbrev ThetaPilotCarrierType : Type umon :=
  I.ThetaPilotPoint D.place.v

/-- The missing primitive package for the deep construction.  The index and
local fields are actual C3 data; the carrier equivalence, measurable space,
measure and its regularity instances are the missing source objects. -/
structure C6TensorProductPrimitive (Y : Type uY) where
  [measurableSpace : MeasurableSpace ((i : iota) → C6TensorLocalField places tuple i)]
  carrierEquiv : Y ≃ ((i : iota) → C6TensorLocalField places tuple i)
  mu : Measure ((i : iota) → C6TensorLocalField places tuple i)
  [finiteMeasureOnCompacts : IsFiniteMeasureOnCompacts mu]
  [openPosMeasure : Measure.IsOpenPosMeasure mu]

attribute [instance] C6TensorProductPrimitive.measurableSpace
attribute [instance] C6TensorProductPrimitive.finiteMeasureOnCompacts
attribute [instance] C6TensorProductPrimitive.openPosMeasure

namespace C6TensorProductPrimitive

variable {Y : Type uY} (P : C6TensorProductPrimitive (places := places) (tuple := tuple) Y)

/-- Construct the C7 C6ProductVolumeData from the actual C3 index/local-field
family plus the primitive carrier equivalence and measure. -/
def toC6ProductVolumeData : C6ProductVolumeData (Y := Y) where
  ι := iota
  finiteIndex := inferInstance
  K := C6TensorLocalField places tuple
  normedField := fun i => inferInstance
  properSpace := fun i => inferInstance
  measurableSpace := P.measurableSpace
  carrierEquiv := P.carrierEquiv
  μ := P.mu
  finiteMeasureOnCompacts := P.finiteMeasureOnCompacts
  openPosMeasure := P.openPosMeasure

@[simp] theorem toC6ProductVolumeData_ι :
    P.toC6ProductVolumeData.ι = iota := rfl

@[simp] theorem toC6ProductVolumeData_K :
    P.toC6ProductVolumeData.K = C6TensorLocalField places tuple := rfl

@[simp] theorem toC6ProductVolumeData_carrierEquiv :
    P.toC6ProductVolumeData.carrierEquiv = P.carrierEquiv := rfl

@[simp] theorem toC6ProductVolumeData_μ :
    P.toC6ProductVolumeData.μ = P.mu := rfl

/-- A primitive package yields a concrete C6ProductVolumeData. -/
theorem nonempty_c6ProductVolumeData : Nonempty (C6ProductVolumeData (Y := Y)) :=
  ⟨P.toC6ProductVolumeData⟩

end C6TensorProductPrimitive

/-- The actual carrier-specific construction at Y = ThetaPilotPoint: the only
missing data are the carrier equivalence and the product measure/regularity
instances for the actual C3 tensor product. -/
theorem c6ProductVolumeDataAtThetaPilotPoint_of_primitive
    (P : C6TensorProductPrimitive (places := places) (tuple := tuple)
      (Y := ThetaPilotCarrierType (I := I) (D := D))) :
    Nonempty (C6ProductVolumeData (Y := ThetaPilotCarrierType (I := I) (D := D))) :=
  ⟨P.toC6ProductVolumeData⟩

/-! ## Exact missing primitive

The actual C3 tensor data supply the finite index iota and the proper normed
local-field family CommonPrimeCompletion (places i (tuple i)).  The native
source does not supply:

1. a MeasurableSpace on the product ((i : iota) -> CommonPrimeCompletion ...);
2. a carrier equivalence
   I.ThetaPilotPoint D.place.v ≃ ((i : iota) -> CommonPrimeCompletion ...);
3. a product Haar measure mu;
4. IsFiniteMeasureOnCompacts mu;
5. Measure.IsOpenPosMeasure mu.

These are exactly the remaining fields of C6TensorProductPrimitive.  The
ThetaPilotPoint carrier is a function type into the value monoid of the prime
strip, not a product of completions, and no production equivalence to the C3
tensor product is present.  No arbitrary index/field/equivalence/measure is
chosen and no unconditional C6ProductVolumeData is constructed. -/

end LeanFormal.IUT.N8Closure.C6ProductVolumeDeep

end
