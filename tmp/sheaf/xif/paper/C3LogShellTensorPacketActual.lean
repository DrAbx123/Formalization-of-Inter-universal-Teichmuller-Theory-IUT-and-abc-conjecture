import tmp.sheaf.xif.paper.PrimeStripLogShellActual
import tmp.sheaf.xif.paper.PaperProcessionNormalization
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithm
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorIntegralRegion
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithm

/-! # Actual C3 tensor packet of local log-shells

IUT III, Proposition 3.2, (ii) (pp. 97-99): the integral structure
I(alpha D_vQ) is obtained by forming direct sums/tensor products of the local
log-shells I(D_v), and IQ(-) is its Q-span.  This file constructs, from the
actual C3 tensor index/places/tuple and the actual local log-shells
(sourceLocalLogShellDatum), the tensor packet of log-shells:

* the actual arithmetic tensor block over C3.tensorIndex at the selected tuple;
* the actual tensor integral region of the local log-shells;
* its compactness;
* its actual additive Haar measure and Haar log-volume;
* the actual Q-span (the IQ operation).

No index comparison V = C3.tensorIndex is used or asserted.  The remaining
missing object for the paper-level capsule is the source prime-strip index/
place comparison, already recorded in PrimeStripLogShellActual.lean.

No arbitrary carrier, sorry, axiom, True, or PUnit is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option synthInstance.maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open MeasureTheory
open scoped BigOperators

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The fiber at a C3 tensor place. -/
abbrev C3LogShellFiber (i : C3.tensorIndex) : Type :=
  CommonPrimeCompletion (c3LogShellPlace C3 i)

/-- The actual arithmetic tensor block over the C3 tensor index and selected
tuple. -/
abbrev C3LogShellTensorBlock : Type :=
  ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple

local instance c3LogShellTensorBlockMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance c3LogShellTensorBlockBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

local instance c3LogShellTensorBlockProperSpace :
    ProperSpace (C3LogShellTensorBlock C3) := inferInstance

local instance c3LogShellTensorBlockLocallyCompactSpace :
    LocallyCompactSpace (C3LogShellTensorBlock C3) := inferInstance

/-- The actual tensor integral region of the local log-shells I(D_v). -/
noncomputable def actualC3LogShellTensorRegion :
    Set (C3LogShellTensorBlock C3) :=
  tensorIntegralRegion (p := C3.p)
    (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)
    (fun i => actualC3LogShell C3 i)

/-- The actual local log-shells are compact, hence their tensor integral
region is compact. -/
theorem actualC3LogShellTensorRegion_compact :
    IsCompact (actualC3LogShellTensorRegion C3) := by
  apply isCompact_tensorIntegralRegion
  intro i
  rw [actualC3LogShell_eq_integralLogShell]
  exact isCompact_integralLogShell (K := C3LogShellFiber C3 i) (p := C3.p)

/-- The actual Q-span of the tensor log-shell region: the IQ operation of
IUT III, Proposition 3.2, (ii). -/
noncomputable def actualC3LogShellTensorIQ :
    Submodule ℚ (C3LogShellTensorBlock C3) :=
  Submodule.span ℚ (actualC3LogShellTensorRegion C3)

/-- The actual additive Haar measure on the tensor block. -/
noncomputable def actualC3LogShellTensorHaar :
    Measure (C3LogShellTensorBlock C3) :=
  Measure.addHaar

/-- The actual Haar measure is additive Haar. -/
instance actualC3LogShellTensorHaar_isAddHaar :
    Measure.IsAddHaarMeasure (actualC3LogShellTensorHaar C3) := by
  unfold actualC3LogShellTensorHaar
  infer_instance

/-- The actual Haar log-volume of the tensor log-shell region. -/
noncomputable def actualC3LogShellTensorLogVolume : Real :=
  (haarLogVolume (actualC3LogShellTensorHaar C3)
    (actualC3LogShellTensorRegion C3)).toReal

/-- The actual C3 tensor packet of log-shells, packaged with its region,
compactness, Q-span and Haar log-volume. -/
structure ActualC3LogShellTensorPacket where
  region : Set (C3LogShellTensorBlock C3)
  region_eq : region = actualC3LogShellTensorRegion C3
  region_compact : IsCompact region
  iqCarrier : Submodule ℚ (C3LogShellTensorBlock C3)
  iqCarrier_eq : iqCarrier = actualC3LogShellTensorIQ C3
  haar : Measure (C3LogShellTensorBlock C3)
  haar_eq : haar = actualC3LogShellTensorHaar C3
  logVolume : Real
  logVolume_eq : logVolume = actualC3LogShellTensorLogVolume C3

namespace ActualC3LogShellTensorPacket

/-- The actual block of the packet. -/
def block (_P : ActualC3LogShellTensorPacket (C3 := C3)) : Type :=
  C3LogShellTensorBlock C3

end ActualC3LogShellTensorPacket

/-- The actual tensor packet of log-shells from the C3 data. -/
noncomputable def actualC3LogShellTensorPacket :
    ActualC3LogShellTensorPacket (C3 := C3) where
  region := actualC3LogShellTensorRegion C3
  region_eq := rfl
  region_compact := actualC3LogShellTensorRegion_compact C3
  iqCarrier := actualC3LogShellTensorIQ C3
  iqCarrier_eq := rfl
  haar := actualC3LogShellTensorHaar C3
  haar_eq := rfl
  logVolume := actualC3LogShellTensorLogVolume C3
  logVolume_eq := rfl

end LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual

end
