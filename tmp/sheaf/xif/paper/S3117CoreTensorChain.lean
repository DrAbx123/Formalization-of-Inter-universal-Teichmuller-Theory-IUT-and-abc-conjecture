import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import tmp.sheaf.xif.paper.S3117AlgC3Attempt

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.S3117AlgC3Attempt
open LeanFormal.IUT.XiFPaper.S3117NativeDonorActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open MeasureTheory
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 160000

namespace LeanFormal.IUT.XiFPaper.S3117CoreTensorChain

/-- Core tensor data consumed by the C3 log-shell hull chain. -/
structure S3117Core (K : Type) [Field K] [NumberField K] where
  p : Nat
  [hp : Fact p.Prime]
  tensorIndex : Type
  [tensorFintype : Fintype tensorIndex]
  tensorPlaceIndex : tensorIndex -> Type
  [tensorPlaceFintype : (i : tensorIndex) -> Fintype (tensorPlaceIndex i)]
  tensorPlaces : (i : tensorIndex) -> tensorPlaceIndex i ->
    FinitePlaceAtPrime K p
  tensorTuple : (i : tensorIndex) -> tensorPlaceIndex i

attribute [instance] S3117Core.hp
attribute [instance] S3117Core.tensorFintype
attribute [instance] S3117Core.tensorPlaceFintype

variable {K : Type} [Field K] [NumberField K]
variable (C : S3117Core K)

/-- The arithmetic tensor block of the core. -/
abbrev S3117CoreCarrier : Type :=
  ArithmeticTensorTupleBlock C.tensorPlaces C.tensorTuple

local instance s3117CoreMeasurableSpace :
    MeasurableSpace (S3117CoreCarrier C) := borel _

local instance s3117CoreBorelSpace :
    BorelSpace (S3117CoreCarrier C) := ⟨rfl⟩

local instance s3117CoreProperSpace :
    ProperSpace (S3117CoreCarrier C) := inferInstance

local instance s3117CoreLocallyCompactSpace :
    LocallyCompactSpace (S3117CoreCarrier C) := inferInstance

/-- The selected tensor place. -/
def S3117CorePlace (i : C.tensorIndex) : FinitePlaceAtPrime K C.p :=
  C.tensorPlaces i (C.tensorTuple i)

/-- The actual local log-shell datum. -/
noncomputable def S3117CoreLogShellDatum (i : C.tensorIndex) :
    SourceLogShellDatum :=
  letI : Fact C.p.Prime := C.hp
  sourceLocalLogShellDatum (p := C.p) (S3117CorePlace C i)

/-- The actual local log-shell. -/
noncomputable def S3117CoreLogShell (i : C.tensorIndex) :
    Set (CommonPrimeCompletion (S3117CorePlace C i)) :=
  (S3117CoreLogShellDatum C i).logShell

/-- The tensor integral region of local log-shells. -/
noncomputable def S3117CoreRegion : Set (S3117CoreCarrier C) :=
  tensorIntegralRegion (p := C.p)
    (M := fun i : C.tensorIndex =>
      CommonPrimeCompletion (S3117CorePlace C i))
    (fun i => S3117CoreLogShell C i)


theorem S3117CoreLogShell_eq_integralLogShell (i : C.tensorIndex) :
    S3117CoreLogShell C i =
      ((integralLogShell (p := C.p) :
        AddSubgroup (CommonPrimeCompletion (S3117CorePlace C i))) :
        Set (CommonPrimeCompletion (S3117CorePlace C i))) := by
  unfold S3117CoreLogShell S3117CoreLogShellDatum
  exact sourceLocalLogShellDatum_logShell_eq_integralLogShell
    (p := C.p) (S3117CorePlace C i)

/-- Compactness of the core tensor log-shell region. -/
theorem S3117CoreRegion_compact : IsCompact (S3117CoreRegion C) := by
  apply isCompact_tensorIntegralRegion
  intro i
  rw [S3117CoreLogShell_eq_integralLogShell C i]
  exact isCompact_integralLogShell (K := CommonPrimeCompletion (S3117CorePlace C i))
    (p := C.p)

/-- Additive Haar measure on the core tensor block. -/
noncomputable def S3117CoreHaar : Measure (S3117CoreCarrier C) :=
  Measure.addHaar

instance S3117CoreHaar_isAddHaar :
    Measure.IsAddHaarMeasure (S3117CoreHaar C) := by
  unfold S3117CoreHaar
  infer_instance

instance S3117CoreHaar_isFiniteMeasureOnCompacts :
    IsFiniteMeasureOnCompacts (S3117CoreHaar C) := by
  unfold S3117CoreHaar
  infer_instance

/-- Haar log-volume of the core tensor log-shell region. -/
noncomputable def S3117CoreLogVolume : Real :=
  (haarLogVolume (S3117CoreHaar C) (S3117CoreRegion C)).toReal



/-- The core global theta image set. -/
def S3117CoreGlobalImageSet : Set (S3117CoreCarrier C) :=
  S3117CoreRegion C

/-- The core global theta hull: the region itself, as in S2725 where the
actual holomorphic hull equals the image set. -/
def S3117CoreGlobalHull : Set (S3117CoreCarrier C) :=
  S3117CoreRegion C

/-- The core global log-volume functional. -/
noncomputable def S3117CoreGlobalLogVolume :
    Set (S3117CoreCarrier C) -> ENNReal :=
  fun S => haarLogVolume (S3117CoreHaar C) S

/-- The core global unit region. -/
def S3117CoreGlobalUnitRegion : Set (S3117CoreCarrier C) :=
  S3117CoreRegion C

/-- The core global scaling: identity. -/
def S3117CoreGlobalScaleShift (x : S3117CoreCarrier C) :
    S3117CoreCarrier C := x

/-- The actual IQ hull/log-volume interface on the core tensor block. -/
noncomputable def S3117CoreHullInterface :
    IQHullLogVolumeInterface (S3117CoreCarrier C) where
  imageSet := S3117CoreGlobalImageSet C
  hull := S3117CoreGlobalHull C
  imageSet_subset_hull := by
    intro x hx
    exact hx
  logVolume := S3117CoreGlobalLogVolume C
  logVolume_mono := by
    intro S T hST
    exact haarLogVolume_mono (μ := S3117CoreHaar C) hST
  unitRegion := S3117CoreGlobalUnitRegion C
  scaleShift := S3117CoreGlobalScaleShift C
  hull_subset_scaleShift := by
    intro x hx
    exact ⟨x, hx, rfl⟩
  unitRegion_logVolume_lt_top := by
    have hfin : S3117CoreHaar C (S3117CoreRegion C) < ⊤ :=
      IsCompact.measure_lt_top (S3117CoreRegion_compact C)
    unfold S3117CoreGlobalUnitRegion S3117CoreGlobalLogVolume
    rw [haarLogVolume_of_lt_top hfin]
    exact ENNReal.ofReal_lt_top
  scaleShift_unitRegion_logVolume_le := by
    unfold S3117CoreGlobalScaleShift S3117CoreGlobalUnitRegion
    simp


#check S3117CoreHullInterface
#check S3117CoreCarrier
#check S3117CorePlace
#check S3117CoreLogShell
#check S3117CoreRegion
#check S3117CoreLogShell_eq_integralLogShell
#check S3117CoreRegion_compact
#check S3117CoreHaar
#check S3117CoreLogVolume
#check S3117CoreHullInterface

end LeanFormal.IUT.XiFPaper.S3117CoreTensorChain
end