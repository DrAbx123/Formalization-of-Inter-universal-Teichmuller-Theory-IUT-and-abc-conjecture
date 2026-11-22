import tmp.sheaf.n8.closure.EtaIntegralStructureSourceBridge

/-!
# Eta residue match attempt

The bridge's exact gap was

  EtaIntegralSourceResidueGap X : l.value = residueCharacteristic (badBasePlace X).

Clause B gives coprimality of l.value with the residue characteristic of every
F-place above a bad place.  Choosing a lift of badBasePlace and applying Clause B
therefore proves

  EtaIntegralSourceResidueGap X is FALSE

for every native X.  The equality cannot be assumed; the source would instead
need a selected bad place of residue characteristic l (or a changed base from
p = l.value to the selected residue).

No arbitrary equality is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaResidueMatchAttempt

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.EtaIntegralStructureSourceBridgeRoute
open LeanFormal.IUT.N8Closure.NativeQParameterActual
open LeanFormal.IUT.N8Closure.NativeReductionRestActual
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeContractFieldsActualAttempt
open LeanFormal.IUT.N8Closure.NativePartitionInputsActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source

variable {l : PrimeGeFive}

/-- Clause B coprimality at the selected bad place: l.value is coprime to its
residue characteristic. -/
theorem badBasePlace_coprime_l (X : N8NativeInput l) :
    Nat.Coprime l.value
      (NumberFieldFinitePlace.residueCharacteristic (badBasePlace X)) := by
  have hp : NumberFieldFinitePlace.comap (k := X.S.arithmetic.Fmod)
      (nativeBadLift X (badNativeBadPlace X)) ∈
      X.S.tuple.source.V_mod_bad := by
    rw [nativeBadLift_comap]
    exact (badNativeBadPlace X).2
  have h := X.S.clauseB.residue_characteristic_prime_to_l
    (nativeBadLift X (badNativeBadPlace X)) hp
  simpa [badNativeBadPlace, nativeBadLift_comap] using h

/-- Decisive no-go: the eta residue equality is false for every native X. -/
theorem etaIntegralSourceResidueGap_false (X : N8NativeInput l) :
    ¬ EtaIntegralSourceResidueGap X := by
  intro h
  have hcop := badBasePlace_coprime_l X
  rw [← h] at hcop
  have h1 : l.value = 1 := by simpa using hcop
  have hp : Nat.Prime l.value := (PrimeGeFive.factPrime l).out
  exact hp.ne_one h1

/-- The exact source condition that would be needed to make the residue bridge
true: the selected bad place must itself have residue characteristic l. -/
def EtaResidueMatchSourceCondition (X : N8NativeInput l) : Prop :=
  NumberFieldFinitePlace.residueCharacteristic (badBasePlace X) = l.value

/-- Clause B makes the required source condition equivalent to a false
coprimality with itself, so it cannot be obtained under the current source
data. -/
theorem etaResidueMatchSourceCondition_false (X : N8NativeInput l) :
    ¬ EtaResidueMatchSourceCondition X := by
  intro h
  exact etaIntegralSourceResidueGap_false X h.symm

end LeanFormal.IUT.N8Closure.EtaResidueMatchAttempt
