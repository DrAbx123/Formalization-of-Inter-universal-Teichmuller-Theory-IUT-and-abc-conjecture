import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorIntegralRegion

/-! # P0 native tensor/readout consumer, without C3

Inputs: a prime p, finite index set i, finite place choices V i, a tuple
(i : iota) -> V i, and the selected actual places at p.  The output is the
actual arithmetic tensor tuple block, the tensor integral region of local
log-shells, its compactness, Q-span, Haar measure and Haar log-volume.

No SourcePilotRegionData/C3 value is used.  The old S3137 C3 fields are listed
in c3RequiredFields below as the exact fields not needed by this consumer.
-/

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option synthInstance.maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeTensorConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.Theorem311Source
open MeasureTheory
open scoped BigOperators

variable {K : Type} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable {ι : Type} [Fintype ι]
variable {V : ι -> Type} [∀ i, Fintype (V i)]

/-- The selected actual place at p for a tensor index. -/
abbrev nativeTensorPlace
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) (i : ι) : FinitePlaceAtPrime K p :=
  places i (tuple i)

/-- The actual common-prime completion fiber at a tensor index. -/
abbrev nativeTensorFiber
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) (i : ι) : Type :=
  CommonPrimeCompletion (nativeTensorPlace places tuple i)

/-- The actual tensor block over the place choices and tuple. -/
abbrev NativeTensorBlock
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) : Type :=
  ArithmeticTensorTupleBlock places tuple

local instance nativeTensorBlockMeasurableSpace
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) :
    MeasurableSpace (NativeTensorBlock places tuple) :=
  borel _

local instance nativeTensorBlockBorelSpace
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) :
    BorelSpace (NativeTensorBlock places tuple) :=
  ⟨rfl⟩

local instance nativeTensorBlockProperSpace
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) :
    ProperSpace (NativeTensorBlock places tuple) :=
  inferInstance

local instance nativeTensorBlockLocallyCompactSpace
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) :
    LocallyCompactSpace (NativeTensorBlock places tuple) :=
  inferInstance

/-- The actual local log-shell datum at a selected place. -/
noncomputable def nativeTensorShellDatum
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) (i : ι) : SourceLogShellDatum :=
  letI : Fact p.Prime := inferInstance
  sourceLocalLogShellDatum (p := p) (nativeTensorPlace places tuple i)

/-- The actual tensor integral region of local log-shells. -/
noncomputable def nativeTensorRegion
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) : Set (NativeTensorBlock places tuple) :=
  tensorIntegralRegion (p := p)
    (M := fun i => nativeTensorFiber places tuple i)
    (fun i => (nativeTensorShellDatum places tuple i).logShell)

/-- Compactness of the native tensor region. -/
theorem nativeTensorRegion_compact
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) :
    IsCompact (nativeTensorRegion (p := p) places tuple) := by
  apply isCompact_tensorIntegralRegion
  intro i
  exact (sourceLocalLogShellDatum_logShell_eq_integralLogShell (p := p)
      (nativeTensorPlace places tuple i)) ▸
    isCompact_integralLogShell (K := nativeTensorFiber places tuple i) (p := p)

/-- The actual Q-span (IQ) of the native tensor region. -/
noncomputable def nativeTensorIQ
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) :
    Submodule ℚ (NativeTensorBlock places tuple) :=
  Submodule.span ℚ (nativeTensorRegion (p := p) places tuple)

/-- The actual additive Haar measure on the native tensor block. -/
noncomputable def nativeTensorHaar
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) :
    Measure (NativeTensorBlock places tuple) :=
  Measure.addHaar

instance nativeTensorHaar_isAddHaar
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) :
    Measure.IsAddHaarMeasure (nativeTensorHaar (p := p) places tuple) := by
  unfold nativeTensorHaar
  infer_instance

/-- Haar log-volume of the native tensor region. -/
noncomputable def nativeTensorLogVolume
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) : Real :=
  (haarLogVolume (nativeTensorHaar (p := p) places tuple)
    (nativeTensorRegion (p := p) places tuple)).toReal

theorem nativeTensorHaar_region_lt_top
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) :
    nativeTensorHaar (p := p) places tuple
      (nativeTensorRegion (p := p) places tuple) < ⊤ :=
  (nativeTensorRegion_compact (p := p) places tuple).measure_lt_top

/-- Native tensor/readout packet: block, region, compactness, IQ, Haar,
log-volume. -/
structure NativeTensorPacket
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) where
  region : Set (NativeTensorBlock places tuple)
  region_eq : region = nativeTensorRegion (p := p) places tuple
  region_compact : IsCompact region
  iqCarrier : Submodule ℚ (NativeTensorBlock places tuple)
  iqCarrier_eq : iqCarrier = nativeTensorIQ (p := p) places tuple
  haar : Measure (NativeTensorBlock places tuple)
  haar_eq : haar = nativeTensorHaar (p := p) places tuple
  logVolume : Real
  logVolume_eq : logVolume = nativeTensorLogVolume (p := p) places tuple

/-- The actual native tensor packet, constructed from p/places/tuple only. -/
noncomputable def nativeTensorPacket
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) :
    NativeTensorPacket (p := p) places tuple where
  region := nativeTensorRegion (p := p) places tuple
  region_eq := rfl
  region_compact := nativeTensorRegion_compact (p := p) places tuple
  iqCarrier := nativeTensorIQ (p := p) places tuple
  iqCarrier_eq := rfl
  haar := nativeTensorHaar (p := p) places tuple
  haar_eq := rfl
  logVolume := nativeTensorLogVolume (p := p) places tuple
  logVolume_eq := rfl

/-- Old C3 fields deliberately not used by the native consumer. -/
def c3RequiredFields : List String :=
  [ "SourcePilotRegionData", "C3.q", "C3.qUnit", "C3.tensorIndex", "C3.tensorPlaces",
    "C3.tensorTuple", "C3.p", "C3.hp",
    "C3-derived S3137 normalized q reading", "C3-derived product formula input" ]

theorem c3RequiredFields_length : c3RequiredFields.length = 10 := rfl

#check nativeTensorPlace
#check nativeTensorFiber
#check NativeTensorBlock
#check nativeTensorShellDatum
#check nativeTensorRegion
#check nativeTensorRegion_compact
#check nativeTensorIQ
#check nativeTensorHaar
#check nativeTensorLogVolume
#check NativeTensorPacket
#check nativeTensorPacket
#check c3RequiredFields
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeTensorConsumerActual
end
