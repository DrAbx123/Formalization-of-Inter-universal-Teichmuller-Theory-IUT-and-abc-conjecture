import tmp.sheaf.n8.closure.C7Interface
import tmp.sheaf.n8.closure.SourceWitnessedOutput
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull
import Mathlib

/-! # C6ProductVolumeData actual attempt (structural projections)

The C7 interface C6ProductVolumeData has exactly the following fields:
an index iota with Finite, a field family K with NormedField and ProperSpace
instances, a measurable product space, a carrier equivalence
Y ≃ ((i : iota) -> K i), a product Haar measure mu, and
IsFiniteMeasureOnCompacts and Measure.IsOpenPosMeasure instances for mu.

This file defines only structural projections from an arbitrary
C6ProductVolumeData.  It does not synthesize typeclass instances or construct
a product measure typeclass, so the projections are type-correct by the
interface fields themselves.  It does not supply a native product index,
field family, carrier equivalence, or measure, and does not fabricate one.

No True/PUnit/axiom/sorry; no arbitrary data. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.N8Closure.C6ProductVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open ABCBridge.N8.C7Actual
open ABCBridge.N8.C4Actual
open MeasureTheory

universe ua uv upi umon ui uL uY uK

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} [Group Label]
variable {D : SourceWitnessedOutputData I Label}

/-- The actual carrier type for the C3 tensor block. -/
abbrev ThetaPilotCarrierType : Type umon :=
  I.ThetaPilotPoint D.place.v

/-- The finite product index carried by a C6ProductVolumeData. -/
def c6ProductIndex {Y : Type uY} (C : C6ProductVolumeData Y) : Type ui :=
  C.ι

/-- The finite-instantiation fact for the product index. -/
theorem c6ProductIndex_finite {Y : Type uY} (C : C6ProductVolumeData Y) :
    Finite C.ι :=
  C.finiteIndex

/-- The local-field family carried by a C6ProductVolumeData. -/
def c6ProductLocalField {Y : Type uY} (C : C6ProductVolumeData Y) :
    C.ι → Type uK :=
  C.K

/-- The proper-space fact for each local field. -/
theorem c6ProductLocalField_proper {Y : Type uY} (C : C6ProductVolumeData Y)
    (i : C.ι) : ProperSpace (C.K i) :=
  C.properSpace i

/-- The carrier equivalence carried by a C6ProductVolumeData. -/
def c6ProductCarrierEquiv {Y : Type uY} (C : C6ProductVolumeData Y) :
    Y ≃ ((i : C.ι) → C.K i) :=
  C.carrierEquiv

/-- The product Haar measure carried by a C6ProductVolumeData, with the
measurable structure supplied by the structure field. -/
def c6ProductMeasure {Y : Type uY} (C : C6ProductVolumeData Y) :
    @Measure ((i : C.ι) → C.K i) C.measurableSpace :=
  C.μ

/-- The raw finite-measure-on-compacts witness, as the interface field. -/
def c6ProductFiniteOnCompactsWitness {Y : Type uY}
    (C : C6ProductVolumeData Y) :=
  C.finiteMeasureOnCompacts

/-- The raw open-positive measure witness, as the interface field. -/
def c6ProductOpenPosWitness {Y : Type uY} (C : C6ProductVolumeData Y) :=
  C.openPosMeasure

/-! ## Exact remaining primitive fields

At Y = I.ThetaPilotPoint D.place.v, the interface requires, and the native
source does not supply, the following primitive fields:

1. the finite product index iota;
2. the family K : iota -> Type with NormedField instances;
3. ProperSpace instances for K;
4. a MeasurableSpace on ((i : iota) -> K i);
5. a carrier equivalence ThetaPilotPoint ≃ ((i : iota) -> K i);
6. a Haar measure mu on the product;
7. IsFiniteMeasureOnCompacts mu;
8. Measure.IsOpenPosMeasure mu.

These are exactly the fields of C6ProductVolumeData.  The projections above
extract them from any hypothetical instance; no native instance is
constructed. -/

end LeanFormal.IUT.N8Closure.C6ProductVolumeActual

end
