import tmp.sheaf.n8.closure.EtaIntegralStructureS
import tmp.sheaf.n8.closure.NativeQParameterActual

/-!
# ETA-6b: source bridge from integral structure S to native q/selected places

Actual bridge: the canonical S (integralLogShell + logShellVolumeConsumer +
finiteOutput Ind laws) is paired with

- the native selected bad place badPlace X;
- the native Tate qParameter at the corresponding bad moduli place.

No free subset is introduced: the eta component is definitionally the canonical
etaIntegralStructureS l.  The local-field/residue compatibility between S's
base Q_[l.value] and the selected native completion is recorded as exact gap
propositions, not assumed.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaIntegralStructureSourceBridgeRoute

open scoped Padic

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.EtaIntegralStructureSRoute
open LeanFormal.IUT.N8Closure.NativeQParameterActual
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeContractFieldsActualAttempt
open LeanFormal.IUT.N8Closure.NativePartitionInputsActual
open LeanFormal.IUT.N8Closure.NativeBadFintypeSourceAttempt
open LeanFormal.IUT.N8Closure.NativeBadFiniteTargetCorrection
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.ConcreteFiniteTheorem311
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source

variable {l : PrimeGeFive}
local instance : Fact (Nat.Prime l.value) := l.factPrime
variable {X : N8NativeInput l}

/-- The native bad moduli place as the corresponding NativeBadPlaces element. -/
def badNativeBadPlace (X : N8NativeInput l) : NativeBadPlaces X :=
  ⟨badBasePlace X, badBasePlace_mem X⟩

/-- Actual source bridge/readout interface: canonical S + native selected place
+ native qParameter. -/
structure EtaIntegralStructureSourceBridge (X : N8NativeInput l) where
  eta : EtaIntegralStructureS l
  eta_eq_canonical : eta = etaIntegralStructureS l
  selected : NativePlaces X.S
  selected_eq_badPlace : selected = badPlace X
  q : Real
  q_eq_native : q = nativeQParameter X (badNativeBadPlace X)

/-- Actual bridge from canonical S and native selected/q data. -/
noncomputable def etaIntegralStructureSourceBridge
    (X : N8NativeInput l) : EtaIntegralStructureSourceBridge X where
  eta := etaIntegralStructureS l
  eta_eq_canonical := rfl
  selected := badPlace X
  selected_eq_badPlace := rfl
  q := nativeQParameter X (badNativeBadPlace X)
  q_eq_native := rfl

/-- Integral readout: the bridge's integral set is S's integralLogShell. -/
def etaIntegralSet (B : EtaIntegralStructureSourceBridge X) :
    Set ℚ_[l.value] :=
  B.eta.integral

theorem etaIntegralSet_eq_integralLogShell
    (B : EtaIntegralStructureSourceBridge X) :
    etaIntegralSet B =
      (integralLogShell (K := ℚ_[l.value]) (p := l.value) :
        Set ℚ_[l.value]) := by
  rw [etaIntegralSet, B.eta.integral_eq_integralLogShell]

/-- Volume-container index readout. -/
def etaVolumeIndex (B : EtaIntegralStructureSourceBridge X) : Nat :=
  B.eta.volume.index

/-- Ind1/Ind2/Ind3 readouts are exactly the S finite-output laws. -/
theorem etaBridge_ind1 (B : EtaIntegralStructureSourceBridge X)
    (t : finiteLabel l) (c : ProcessionChoice l) :
    B.eta.finite.logVolume (ProcessionChoice.ind1Act t c) =
      B.eta.finite.logVolume c :=
  B.eta.ind1_invariant t c

theorem etaBridge_ind2 (B : EtaIntegralStructureSourceBridge X)
    (t : finiteLabel l) (c : ProcessionChoice l) :
    B.eta.finite.logVolume (ProcessionChoice.ind2Act t c) =
      B.eta.finite.logVolume c :=
  B.eta.ind2_invariant t c

theorem etaBridge_ind3 (B : EtaIntegralStructureSourceBridge X)
    (n : Nat) (c : ProcessionChoice l) :
    B.eta.finite.logVolume c ≤
      B.eta.finite.logVolume (ProcessionChoice.ind3Lift n c) :=
  B.eta.ind3_upper n c

/-- Exact source gap for the base residue: S uses p = l.value, while the
selected native bad place has its own residue characteristic. -/
def EtaIntegralSourceResidueGap (X : N8NativeInput l) : Prop :=
  l.value = NumberFieldFinitePlace.residueCharacteristic (badBasePlace X)

end LeanFormal.IUT.N8Closure.EtaIntegralStructureSourceBridgeRoute
