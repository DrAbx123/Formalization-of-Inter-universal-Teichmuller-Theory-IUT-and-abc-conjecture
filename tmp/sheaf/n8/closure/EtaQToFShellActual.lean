import tmp.sheaf.n8.closure.EtaFPlaceNormalizedComparison
import tmp.sheaf.n8.closure.C1P6QUniformizerNormalization
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers

/-!
# Eta q -> F-shell actual (no Fmod ring equiv)

Uses the actual native F-place normalization:
- fPlaceShell X = sourceLocalLogShellDatum at nativeFPlaceAtPrime X;
- fPlaceVolumeConsumer/fPlaceLogVolume from EtaFPlaceNormalizedComparison;
- qUnitPart from the actual C1P6QUniformizerNormalization of the native q.

The q element itself has valuation < 1 and is not an integral unit, so it cannot
be a shell unit.  The actual normalization unit part is an F-shell unit.  Its
shell logMap value is constructed; membership in the F logShell and nonvanishing
are exact remaining gaps (no arbitrary map).

No Fmod selected-completion ring equivalence is used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaQToFShellActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open LeanFormal.IUT.N8Closure.C1P6QUniformizerNormalization
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual F-shell units at the native F-place. -/
abbrev FShellUnits (X : N8NativeInput l) : Type _ :=
  (fPlaceShell X).Units

/-- Actual q normalization unit at the F-place. -/
noncomputable def qToShellUnit (X : N8NativeInput l) : FShellUnits X :=
  Units.mapEquiv
    ((normalizedCompletionIntegersEquiv (K := X.S.arithmetic.F)
      (nativeFPlaceOverBad X)).symm).toMulEquiv
    (c1P6QUniformizerNormalization X).unit

/-- Actual q-to-F-shell logMap value. -/
noncomputable def qToShellValue (X : N8NativeInput l) : FPlaceCompletion X :=
  ((fPlaceShell X).logMap (qToShellUnit X)).toAdd

/-- Exact value-membership gap: the q normalization unit log lies in the actual
F log-shell. -/
def QToShellValueMem (X : N8NativeInput l) : Prop :=
  qToShellValue X ∈ (fPlaceShell X).logShell

/-- Exact nonvanishing gap for the q-to-shell value. -/
def QToShellValueNeZero (X : N8NativeInput l) : Prop :=
  qToShellValue X ≠ 0

/-- Actual q-to-F-shell packaging: actual normalization unit part, actual
logMap value, plus the two exact remaining properties. -/
structure EtaQToFShellData (X : N8NativeInput l) where
  unitPart : FShellUnits X
  unitPart_eq : unitPart = qToShellUnit X
  value : FPlaceCompletion X
  value_eq : value = qToShellValue X
  value_mem : value ∈ (fPlaceShell X).logShell
  value_ne_zero : value ≠ 0

/-- Exact target: actual q-part-to-F-shell data. -/
def EtaQToFShellTarget (X : N8NativeInput l) : Prop :=
  Nonempty (EtaQToFShellData X)

/-- The q element is not itself an integral shell unit: its valuation is < 1.
The actual map uses the normalization unit part, not the raw q. -/
theorem nativeQ_valuation_lt_one (X : N8NativeInput l) :
    (Valued.v (C9QPilotRegion.nativeQ X).q :
      WithZero (Multiplicative Int)) < 1 :=
  (C9QPilotRegion.nativeQ X).valuation_lt_one

end LeanFormal.IUT.N8Closure.EtaQToFShellActual
