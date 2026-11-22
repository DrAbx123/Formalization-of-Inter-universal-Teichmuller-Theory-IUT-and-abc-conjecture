import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import tmp.sheaf.xif.paper.S1391C3LSourcePilotActual

/-! # A978: L-carrier C3 log-shell tensor packet

The old C3LogShellTensorPacketActual definitions depend on SourcePilotRegionData.
This file adapts the tensor block/region/IQ/Haar/log-volume to the L record
SourcePilotRegionDataL (S1391), whose p/hp/tensorIndex/tensorPlaces/tensorTuple
fields are the same shape. No q/roots are used by the tensor block. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option synthInstance.maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.C3LogShellTensorLActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.Theorem311Source
open MeasureTheory

universe ua upi umon ui

variable {l : PrimeGeFive}
variable {I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)}
variable (C3L : SourcePilotRegionDataL (I := I))

/-- The L-carrier selected tensor place at an index. -/
abbrev C3LogShellPlaceL (i : C3L.tensorIndex) :
    FinitePlaceAtPrime I.initial.arithmetic.Fmod C3L.p :=
  C3L.tensorPlaces i (C3L.tensorTuple i)

/-- The L-carrier fiber at a tensor index. -/
abbrev C3LogShellFiberL (i : C3L.tensorIndex) : Type :=
  CommonPrimeCompletion (C3LogShellPlaceL (I := I) C3L i)

/-- The L-carrier tensor block: the same arithmetic tensor tuple block. -/
abbrev C3LogShellTensorBlockL : Type :=
  ArithmeticTensorTupleBlock C3L.tensorPlaces C3L.tensorTuple

local instance c3LogShellTensorBlockLMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlockL C3L) := borel _

local instance c3LogShellTensorBlockLBorelSpace :
    BorelSpace (C3LogShellTensorBlockL C3L) := ⟨rfl⟩

local instance c3LogShellTensorBlockLProperSpace :
    ProperSpace (C3LogShellTensorBlockL C3L) := inferInstance

local instance c3LogShellTensorBlockLLocallyCompactSpace :
    LocallyCompactSpace (C3LogShellTensorBlockL C3L) := inferInstance

/-- The L-carrier actual local log-shell datum at a tensor index. -/
noncomputable def actualC3LogShellDatumL (i : C3L.tensorIndex) : SourceLogShellDatum :=
  letI : Fact C3L.p.Prime := C3L.hp
  sourceLocalLogShellDatum (p := C3L.p) (C3LogShellPlaceL (I := I) C3L i)

/-- The L-carrier actual local log-shell. -/
noncomputable def actualC3LogShellL (i : C3L.tensorIndex) :
    Set (C3LogShellFiberL (I := I) C3L i) :=
  (actualC3LogShellDatumL (I := I) C3L i).logShell

/-- The L-carrier local log-shell is the integral log-shell. -/
theorem actualC3LogShellL_eq_integralLogShell (i : C3L.tensorIndex) :
    actualC3LogShellL (I := I) C3L i =
      ((integralLogShell (p := C3L.p) :
        AddSubgroup (C3LogShellFiberL (I := I) C3L i)) :
        Set (C3LogShellFiberL (I := I) C3L i)) := by
  unfold actualC3LogShellL actualC3LogShellDatumL
  exact sourceLocalLogShellDatum_logShell_eq_integralLogShell
    (p := C3L.p) (C3LogShellPlaceL (I := I) C3L i)

/-- The L-carrier actual tensor integral region of local log-shells. -/
noncomputable def actualC3LogShellTensorRegionL :
    Set (C3LogShellTensorBlockL (I := I) C3L) :=
  tensorIntegralRegion (p := C3L.p)
    (M := fun i : C3L.tensorIndex => C3LogShellFiberL (I := I) C3L i)
    (fun i => actualC3LogShellL (I := I) C3L i)

/-- Compactness of the L-carrier tensor region. -/
theorem actualC3LogShellTensorRegionL_compact :
    IsCompact (actualC3LogShellTensorRegionL (I := I) C3L) := by
  apply isCompact_tensorIntegralRegion
  intro i
  rw [actualC3LogShellL_eq_integralLogShell]
  exact isCompact_integralLogShell (K := C3LogShellFiberL (I := I) C3L i) (p := C3L.p)

/-- The L-carrier Q-span (IQ operation). -/
noncomputable def actualC3LogShellTensorIQL :
    Submodule ℚ (C3LogShellTensorBlockL (I := I) C3L) :=
  Submodule.span ℚ (actualC3LogShellTensorRegionL (I := I) C3L)

/-- The L-carrier additive Haar measure. -/
noncomputable def actualC3LogShellTensorHaarL :
    Measure (C3LogShellTensorBlockL (I := I) C3L) :=
  Measure.addHaar

instance actualC3LogShellTensorHaarL_isAddHaar :
    Measure.IsAddHaarMeasure (actualC3LogShellTensorHaarL (I := I) C3L) := by
  unfold actualC3LogShellTensorHaarL
  infer_instance

/-- The L-carrier tensor region has finite Haar measure (compactness). -/
theorem actualC3LogShellTensorHaarL_lt_top :
    actualC3LogShellTensorHaarL (I := I) C3L
      (actualC3LogShellTensorRegionL (I := I) C3L) < ⊤ :=
  (actualC3LogShellTensorRegionL_compact (I := I) C3L).measure_lt_top

/-- The L-carrier Haar measure is a positive additive Haar measure (by type). -/
theorem actualC3LogShellTensorHaarL_isAddHaarMeasure :
    Measure.IsAddHaarMeasure (actualC3LogShellTensorHaarL (I := I) C3L) :=
  inferInstance

/-- The L-carrier Haar log-volume of the tensor region. -/
noncomputable def actualC3LogShellTensorLogVolumeL : Real :=
  (haarLogVolume (actualC3LogShellTensorHaarL (I := I) C3L)
    (actualC3LogShellTensorRegionL (I := I) C3L)).toReal

/-- The L-carrier tensor packet of log-shells. -/
structure ActualC3LogShellTensorPacketL where
  region : Set (C3LogShellTensorBlockL (I := I) C3L)
  region_eq : region = actualC3LogShellTensorRegionL (I := I) C3L
  region_compact : IsCompact region
  iqCarrier : Submodule ℚ (C3LogShellTensorBlockL (I := I) C3L)
  iqCarrier_eq : iqCarrier = actualC3LogShellTensorIQL (I := I) C3L
  haar : Measure (C3LogShellTensorBlockL (I := I) C3L)
  haar_eq : haar = actualC3LogShellTensorHaarL (I := I) C3L
  logVolume : Real
  logVolume_eq : logVolume = actualC3LogShellTensorLogVolumeL (I := I) C3L

/-- The actual L-carrier tensor packet. -/
noncomputable def actualC3LogShellTensorPacketL :
    ActualC3LogShellTensorPacketL (I := I) C3L where
  region := actualC3LogShellTensorRegionL (I := I) C3L
  region_eq := rfl
  region_compact := actualC3LogShellTensorRegionL_compact (I := I) C3L
  iqCarrier := actualC3LogShellTensorIQL (I := I) C3L
  iqCarrier_eq := rfl
  haar := actualC3LogShellTensorHaarL (I := I) C3L
  haar_eq := rfl
  logVolume := actualC3LogShellTensorLogVolumeL (I := I) C3L
  logVolume_eq := rfl

end LeanFormal.IUT.XiFPaper.C3LogShellTensorLActual
