import tmp.sheaf.n8.closure.EtaComparisonNontrivial
import tmp.sheaf.n8.closure.EtaAnabAtFPlace
import tmp.sheaf.n8.closure.EtaValueGroupLineActual
import Mathlib

/-!
# O2: independent eta^q and eta^anab constructions and comparison

Two independent actual maps:

* etaQMap : units of the native F-completion -> Multiplicative R,
  unit norm log degree (the actual q-sided eta^q map);
* etaAnabMap : Multiplicative R -> Multiplicative R,
  the actual F-place etaAnab log-volume readout of EtaAnabAtFPlace.

They have different domains and are not defined as inverses.  The comparison is
at the actual q-unit / actual q pilot.  It reduces exactly to the missing
source identification of the F-place etaAnab log-volume with the native q
pilot; that is the decisive no-go/gap.  No local wrapper and no arbitrary
comparison map are introduced.
-/

noncomputable section

namespace ABCBridge.N8.O2EtaIndependent

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQActual
open LeanFormal.IUT.N8Closure.EtaValueGroupLineActual
open LeanFormal.IUT.N8Closure.EtaAnabAtFPlace
open LeanFormal.IUT.N8Closure.EtaComparisonNontrivial
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual eta^q map: unit norm log degree on the native F-completion units. -/
noncomputable def etaQMap : LeanFormal.IUT.N8Closure.EtaQActual.Rval (X := X) → Multiplicative ℝ :=
  fun u => unitNormLogDegree (Completion (nativeFPlaceOverBad X)) u

/-- Actual eta^anab map: F-place etaAnab log-volume readout, independent of
etaQMap and with the other domain. -/
noncomputable def etaAnabMap : Rval → Multiplicative ℝ :=
  fun _ => Multiplicative.ofAdd (etaRssAtFPlace (X := X)).logVolume

/-- The two maps are at the actual q-unit and actual q pilot. -/
def O2ComparisonAtPilot : Prop :=
  etaQMap X (LeanFormal.IUT.N8Closure.EtaQActual.etaQUnit (X := X)) =
    etaAnabMap X (LeanFormal.IUT.N8Closure.EtaValueGroupLineActual.etaPilot (X := X))

/-- Actual etaQ value at the q-unit is the q pilot. -/
theorem etaQMap_qUnit :
    etaQMap X (LeanFormal.IUT.N8Closure.EtaQActual.etaQUnit (X := X)) =
      LeanFormal.IUT.N8Closure.EtaValueGroupLineActual.etaPilot (X := X) := by
  change unitNormLogDegree (Completion (nativeFPlaceOverBad X))
      (LeanFormal.IUT.N8Closure.EtaQActual.etaQUnit (X := X)) =
    LeanFormal.IUT.N8Closure.EtaValueGroupLineActual.etaPilot (X := X)
  simp [LeanFormal.IUT.N8Closure.EtaQActual.etaQUnit,
    LeanFormal.IUT.N8Closure.EtaValueGroupLineActual.etaPilot,
    qPilotKummerRelativeVolume, nativeQUnitActual]

/-- Exact reduction of the O2 comparison to the actual F-place etaAnab
log-volume identification. -/
theorem o2Comparison_iff :
    O2ComparisonAtPilot X ↔
      LeanFormal.IUT.N8Closure.EtaValueGroupLineActual.etaPilot (X := X) =
        Multiplicative.ofAdd (etaRssAtFPlace (X := X)).logVolume := by
  unfold O2ComparisonAtPilot etaAnabMap
  rw [etaQMap_qUnit]

/-- The decisive O2 gap: the actual F-place etaAnab log-volume equals the
native q pilot in the value-group line.  No production construction proves
this identification; it is the missing source comparison. -/
def O2MissingSourceIdentification : Prop :=
  LeanFormal.IUT.N8Closure.EtaValueGroupLineActual.etaPilot (X := X) =
    Multiplicative.ofAdd (etaRssAtFPlace (X := X)).logVolume

/-- Exact no-go record: the O2 comparison is equivalent to the missing source
identification.  Neither side is an arbitrary map. -/
theorem o2Comparison_iff_missingSource :
    O2ComparisonAtPilot X ↔ O2MissingSourceIdentification X :=
  o2Comparison_iff X

end ABCBridge.N8.O2EtaIndependent
