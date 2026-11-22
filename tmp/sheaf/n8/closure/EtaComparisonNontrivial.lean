import tmp.sheaf.n8.closure.EtaQActual
import tmp.sheaf.n8.closure.EtaValueGroupLineActual
import tmp.sheaf.n8.closure.C9QPilotRegion

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# ETA nontrivial comparison target

Defines independent etaQ and etaAnab map interfaces and a nontrivial
comparison target: the q-unit image and the pilot image agree in the common
value-group line.  The target is a commutative value equality, NOT inverse
laws `etaAnab ∘ etaQ = id` or `etaQ ∘ etaAnab = id`.

The etaQ interface is actual (unit norm log degree).  The independent etaAnab
interface has no production construction and is the exact named gap.
-/

noncomputable section

open MeasureTheory BigOperators
open IsDedekindDomain NumberField
open scoped NumberField
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQActual
open LeanFormal.IUT.N8Closure.EtaValueGroupLineActual

namespace LeanFormal.IUT.N8Closure.EtaComparisonNontrivial

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Independent etaQ map interface: q-side carrier -> real value-group line. -/
structure EtaQMapInterface (X : N8NativeInput l) where
  etaQ : EtaQActual.Rval (X := X) → Multiplicative ℝ

/-- Independent etaAnab map interface: real value-group line -> real value-group
line.  This is a separate map, not the inverse of etaQ. -/
structure EtaAnabMapInterface (X : N8NativeInput l) where
  etaAnab : Multiplicative ℝ → Multiplicative ℝ

/-- Actual etaQ interface from the unit norm log degree. -/
noncomputable def etaQMapInterface : EtaQMapInterface (X := X) where
  etaQ := fun u => unitNormLogDegree (Completion (nativeFPlaceOverBad X)) u

theorem etaQMapInterface_qUnit :
    (etaQMapInterface (X := X)).etaQ (EtaQActual.etaQUnit (X := X)) =
      EtaValueGroupLineActual.etaPilot (X := X) := by
  change unitNormLogDegree (Completion (nativeFPlaceOverBad X))
      (EtaQActual.etaQUnit (X := X)) =
    EtaValueGroupLineActual.etaPilot (X := X)
  simp [EtaQActual.etaQUnit, EtaValueGroupLineActual.etaPilot,
    C9QPilotRegion.qPilotKummerRelativeVolume, NativeC3.nativeQUnitActual]

/-- Nontrivial comparison target: the independent etaQ and etaAnab interfaces
have equal values at the actual q-unit and actual pilot respectively.  No
inverse-law field is present. -/
structure EtaComparisonNontrivial (X : N8NativeInput l) where
  qInterface : EtaQMapInterface (X := X)
  anabInterface : EtaAnabMapInterface (X := X)
  value_eq : qInterface.etaQ (EtaQActual.etaQUnit (X := X)) =
    anabInterface.etaAnab (EtaValueGroupLineActual.etaPilot (X := X))

/-- The nontrivial comparison target exists as soon as the independent etaAnab
interface is supplied together with its actual pilot value.  etaQ is actual. -/
theorem etaComparisonNontrivial_of_anab
    (A : EtaAnabMapInterface (X := X))
    (hvalue : A.etaAnab (EtaValueGroupLineActual.etaPilot (X := X)) =
      EtaValueGroupLineActual.etaPilot (X := X)) :
    Nonempty (EtaComparisonNontrivial (X := X)) := by
  refine ⟨⟨etaQMapInterface (X := X), A, ?_⟩⟩
  rw [etaQMapInterface_qUnit]
  exact hvalue.symm

end LeanFormal.IUT.N8Closure.EtaComparisonNontrivial

end