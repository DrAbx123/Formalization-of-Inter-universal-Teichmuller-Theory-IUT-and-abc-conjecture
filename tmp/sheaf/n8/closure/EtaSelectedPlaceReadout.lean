import tmp.sheaf.n8.closure.EtaIntegralStructureAtSelectedPlace

/-!
# Selected-place log-shell/log-volume readout and etaPilot/native q gap

The actual corrected S at the selected bad native place supplies:
- a selected log-shell set (its production integralLogShell at SelectedCompletion);
- a selected log-volume readout derived from the production
  LogShellVolumeConsumer index;
- the native qParameter at the same selected bad place.

The etaPilot/native-q comparison is recorded as an exact equality gap
(etaSelectedLogVolume X = etaPilotQ X); it is not assumed and no common Real
carrier or arbitrary readout is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaSelectedPlaceReadoutRoute

open scoped Padic

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeQParameterActual
open LeanFormal.IUT.N8Closure.NativeContractFieldsActualAttempt
open LeanFormal.IUT.N8Closure.NativePartitionInputsActual
open LeanFormal.IUT.N8Closure.NativeBadFintypeSourceAttempt
open LeanFormal.IUT.N8Closure.NativeBadFiniteTargetCorrection
open LeanFormal.IUT.N8Closure.NativeReductionRestActual
open LeanFormal.IUT.N8Closure.EtaIntegralStructureAtSelectedPlaceRoute
open LeanFormal.IUT.N8Closure.EtaIntegralStructureSourceBridgeRoute
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.Foundations.LocalFields.LogShellVolume
open LeanFormal.IUT.ConcreteFiniteTheorem311

variable {l : PrimeGeFive}
variable {X : N8NativeInput l}

/-- Actual selected-place readout: selected log-shell set, volume index and
log-volume, and the native qParameter at the same selected bad place. -/
structure EtaSelectedPlaceReadout (X : N8NativeInput l) where
  selected : NativePlaces X.S
  selected_eq_badPlace : selected = badPlace X
  q : Real
  q_eq_native : q = nativeQParameter X (badNativeBadPlace X)
  shell : Set (SelectedCompletion X)
  shell_eq_integral :
    shell = (etaIntegralStructureAtSelectedPlace X).integral
  volumeIndex : Nat
  volumeIndex_eq :
    volumeIndex = (etaIntegralStructureAtSelectedPlace X).volume.index
  logVolume : Real
  logVolume_eq : logVolume = Real.log (volumeIndex : Real)

/-- Actual selected-place readout from corrected S and native q. -/
noncomputable def etaSelectedPlaceReadout (X : N8NativeInput l) :
    EtaSelectedPlaceReadout X where
  selected := badPlace X
  selected_eq_badPlace := rfl
  q := nativeQParameter X (badNativeBadPlace X)
  q_eq_native := rfl
  shell := (etaIntegralStructureAtSelectedPlace X).integral
  shell_eq_integral := rfl
  volumeIndex := (etaIntegralStructureAtSelectedPlace X).volume.index
  volumeIndex_eq := rfl
  logVolume := Real.log
    ((etaIntegralStructureAtSelectedPlace X).volume.index : Real)
  logVolume_eq := rfl

/-- Selected log-shell readout. -/
def etaSelectedLogShell (X : N8NativeInput l) :
    Set (SelectedCompletion X) :=
  (etaSelectedPlaceReadout X).shell

/-- Selected log-volume readout from the actual volume-container index. -/
def etaSelectedLogVolume (X : N8NativeInput l) : Real :=
  (etaSelectedPlaceReadout X).logVolume

/-- Native q-pilot value at the selected bad place. -/
def etaPilotQ (X : N8NativeInput l) : Real :=
  (etaSelectedPlaceReadout X).q

/-- Exact etaPilot/native-q comparison gap: the selected log-volume readout
equals the native q-parameter.  It is not assumed. -/
def EtaSelectedPlaceQPilotGap (X : N8NativeInput l) : Prop :=
  etaSelectedLogVolume X = etaPilotQ X

end LeanFormal.IUT.N8Closure.EtaSelectedPlaceReadoutRoute
