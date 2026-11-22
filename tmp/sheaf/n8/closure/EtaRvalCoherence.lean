import tmp.sheaf.n8.closure.EtaQActual
import tmp.sheaf.n8.closure.EtaValueGroupLineActual
import tmp.sheaf.n8.closure.C9QPilotRegion

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# ETA Rval coherence: completion units -> real value group

Constructs the canonical actual map from ETA-3 `Rval = completion units` to
ETA-5 `Rval = Multiplicative Real` using `unitNormLogDegree`, and proves that
the native q-unit/image is exactly the ETA-5 `etaPilot`.  No free map is
introduced.

The converse real-to-completion-units map is not asserted; it has no canonical
construction (the norm-log map is not injective on completion units).
-/

noncomputable section

open MeasureTheory BigOperators
open IsDedekindDomain NumberField
open scoped NumberField
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQActual
open LeanFormal.IUT.N8Closure.EtaValueGroupLineActual

namespace LeanFormal.IUT.N8Closure.EtaRvalCoherence

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Canonical actual map: completion units -> `Multiplicative ℝ` via the
ordinary unit norm log degree. -/
noncomputable def etaQRvalToValueGroup :
    EtaQActual.Rval (X := X) → Multiplicative ℝ :=
  fun u => unitNormLogDegree (Completion (nativeFPlaceOverBad X)) u

theorem etaQRvalToValueGroup_apply (u : EtaQActual.Rval (X := X)) :
    etaQRvalToValueGroup (X := X) u =
      unitNormLogDegree (Completion (nativeFPlaceOverBad X)) u := rfl

/-- The native q-unit maps to exactly the ETA-5 pilot. -/
theorem etaQUnit_image_eq_etaPilot :
    etaQRvalToValueGroup (X := X) (EtaQActual.etaQUnit (X := X)) =
      EtaValueGroupLineActual.etaPilot (X := X) := by
  rfl

/-- Exact coherence data between ETA-3 and ETA-5 Rval carriers. -/
structure EtaRvalCoherence (X : N8NativeInput l) where
  /-- Actual map between the two Rval carriers. -/
  toValueGroup : EtaQActual.Rval (X := X) → Multiplicative ℝ
  /-- The map is the canonical norm-log map, not a free choice. -/
  toValueGroup_eq : toValueGroup = etaQRvalToValueGroup (X := X)
  /-- The q-unit image is the ETA-5 pilot. -/
  qUnit_image_eq : toValueGroup (EtaQActual.etaQUnit (X := X)) =
    EtaValueGroupLineActual.etaPilot (X := X)

/-- Actual construction of the coherence data. -/
noncomputable def etaRvalCoherence : EtaRvalCoherence (X := X) where
  toValueGroup := etaQRvalToValueGroup (X := X)
  toValueGroup_eq := rfl
  qUnit_image_eq := etaQUnit_image_eq_etaPilot (X := X)

theorem etaRvalCoherence_nonempty :
    Nonempty (EtaRvalCoherence (X := X)) :=
  ⟨etaRvalCoherence (X := X)⟩

/-- Unified etaQ/etaPilot interface: actual q-side data plus the canonical map
and its q-unit/pilot relation. -/
structure EtaUnifiedInterface (X : N8NativeInput l) where
  qData : EtaQActual.EtaQActualData (X := X)
  coherence : EtaRvalCoherence (X := X)
  qUnit_image_eq : coherence.toValueGroup qData.qUnit =
    EtaValueGroupLineActual.etaPilot (X := X)

/-- Actual unified interface from the actual coherence and any etaQ map data. -/
noncomputable def etaUnifiedInterface_of_map
    (M : EtaQActual.RvalToRssQMap (X := X)) :
    EtaUnifiedInterface (X := X) := by
  let qData := EtaQActual.etaQActualData_of_map (X := X) M
  let coh := etaRvalCoherence (X := X)
  exact ⟨qData, coh, by
    change etaQRvalToValueGroup (X := X)
      (EtaQActual.etaQUnit (X := X)) =
      EtaValueGroupLineActual.etaPilot (X := X)
    exact etaQUnit_image_eq_etaPilot (X := X)⟩

/-- Exact no-go target for the converse map: no canonical inverse of the
norm-log map is constructed.  This is the missing real->completion-units map;
it is not a free map. -/
def MissingValueGroupToEtaQRvalMap : Prop :=
  ¬ ∃ f : Multiplicative ℝ → EtaQActual.Rval (X := X),
      Function.LeftInverse f (etaQRvalToValueGroup (X := X))

end LeanFormal.IUT.N8Closure.EtaRvalCoherence

end
