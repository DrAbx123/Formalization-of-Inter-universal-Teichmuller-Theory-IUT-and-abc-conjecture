import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogShellVolumeConsumer
import LeanFormal.IUT.IUTIII.Theorem311.ConcreteFiniteModel
import tmp.sheaf.n8.closure.NativeQParameterActual
import tmp.sheaf.n8.closure.EtaIntegralStructureS
import tmp.sheaf.n8.closure.EtaIntegralStructureSourceBridge

/-!
# ETA corrected S at the selected bad native place

The previous S was fixed at Q_[l.value].  Clause B proves
l.value != residueCharacteristic (badBasePlace X), so that base is wrong.

Correction: use the actual selected bad native place's finite completion

  SelectedCompletion X := CommonPrimeCompletion (badBasePlace X, p),

where p := (completionRationalPrime (badBasePlace X)).val is the actual
completion rational prime.  This is an actual local field with all local-field
instances supplied by production, and the integral structure is its production
integralLogShell; the volume container and Ind1/2/3 laws are the production
ones.  No arbitrary local field, base change, or residue equality is assumed.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaIntegralStructureAtSelectedPlaceRoute

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
open LeanFormal.IUT.N8Closure.EtaIntegralStructureSRoute
open LeanFormal.IUT.N8Closure.EtaIntegralStructureSourceBridgeRoute
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.Foundations.LocalFields.LogShellVolume
open LeanFormal.IUT.ConcreteFiniteTheorem311

variable {l : PrimeGeFive}
variable {X : N8NativeInput l}

/-- Actual completion rational prime at the selected native bad place. -/
abbrev selectedBadPrime (X : N8NativeInput l) : Nat :=
  (completionRationalPrime (badBasePlace X)).val

local instance selectedBadPrime_fact (X : N8NativeInput l) :
    Fact (Nat.Prime (selectedBadPrime X)) :=
  completionRationalPrime_fact (badBasePlace X)

/-- The selected native bad place as a finite-place-at-prime. -/
def selectedBadPlaceAtPrime (X : N8NativeInput l) :
    FinitePlaceAtPrime (K := X.S.arithmetic.Fmod) (selectedBadPrime X) :=
  ⟨badBasePlace X, rfl⟩

/-- Actual local completion at the selected native bad place. -/
abbrev SelectedCompletion (X : N8NativeInput l) : Type :=
  CommonPrimeCompletion (selectedBadPlaceAtPrime X)

/-- Corrected integral structure at the selected native bad place. -/
structure EtaIntegralStructureAtSelectedPlace (X : N8NativeInput l) where
  selected : NativePlaces X.S
  selected_eq : selected = badPlace X
  q : Real
  q_eq_native : q = nativeQParameter X (badNativeBadPlace X)
  integral : Set (SelectedCompletion X)
  integral_eq_integralLogShell :
    integral = (integralLogShell (K := SelectedCompletion X)
      (p := selectedBadPrime X) : Set (SelectedCompletion X))
  volume : LogShellVolumeConsumer (K := SelectedCompletion X)
    (p := selectedBadPrime X)
  finite : FiniteOutput l
  ind1_invariant : ∀ t c,
    finite.logVolume (ProcessionChoice.ind1Act t c) = finite.logVolume c
  ind2_invariant : ∀ t c,
    finite.logVolume (ProcessionChoice.ind2Act t c) = finite.logVolume c
  ind3_upper : ∀ n c,
    finite.logVolume c ≤ finite.logVolume (ProcessionChoice.ind3Lift n c)

/-- Actual corrected S: selected bad place, its actual completion, intact
integralLogShell/volume/Ind laws.  No residue equality is used. -/
noncomputable def etaIntegralStructureAtSelectedPlace
    (X : N8NativeInput l) : EtaIntegralStructureAtSelectedPlace X where
  selected := badPlace X
  selected_eq := rfl
  q := nativeQParameter X (badNativeBadPlace X)
  q_eq_native := rfl
  integral := (integralLogShell (K := SelectedCompletion X)
    (p := selectedBadPrime X) : Set (SelectedCompletion X))
  integral_eq_integralLogShell := rfl
  volume := logShellVolumeConsumer (K := SelectedCompletion X)
    (p := selectedBadPrime X)
  finite := finiteOutput l
  ind1_invariant := (finiteOutput l).ind1_invariant
  ind2_invariant := (finiteOutput l).ind2_invariant
  ind3_upper := (finiteOutput l).ind3_upper

theorem integral_eq_integralLogShell_atSelected
    (B : EtaIntegralStructureAtSelectedPlace X) :
    B.integral = (integralLogShell (K := SelectedCompletion X)
      (p := selectedBadPrime X) : Set (SelectedCompletion X)) :=
  B.integral_eq_integralLogShell

theorem etaAtSelected_ind1 (B : EtaIntegralStructureAtSelectedPlace X)
    (t : finiteLabel l) (c : ProcessionChoice l) :
    B.finite.logVolume (ProcessionChoice.ind1Act t c) =
      B.finite.logVolume c :=
  B.ind1_invariant t c

theorem etaAtSelected_ind2 (B : EtaIntegralStructureAtSelectedPlace X)
    (t : finiteLabel l) (c : ProcessionChoice l) :
    B.finite.logVolume (ProcessionChoice.ind2Act t c) =
      B.finite.logVolume c :=
  B.ind2_invariant t c

theorem etaAtSelected_ind3 (B : EtaIntegralStructureAtSelectedPlace X)
    (n : Nat) (c : ProcessionChoice l) :
    B.finite.logVolume c ≤
      B.finite.logVolume (ProcessionChoice.ind3Lift n c) :=
  B.ind3_upper n c

end LeanFormal.IUT.N8Closure.EtaIntegralStructureAtSelectedPlaceRoute
