import tmp.sheaf.n8.closure.EtaValueGroupLineActual

/-!
# EtaComparisonReduction

ETA-8e: exact reduction of the eta comparison to the actual pilot and its
selected places, using the actual `Rval = Multiplicative ℝ` and native q-pilot
from `EtaValueGroupLineActual`.

`EtaComparisonAtPilot` is the comparison of the two eta maps only at the
actual pilot.  A full function equality reduces to the pilot comparison by
evaluation (one-way, actual).  The converse is not asserted: the eta maps are
the exact missing ETA source objects (`EtaComparisonMaps`), recorded as a
named gap.  No direct Q/hull comparison, no trivial Real line, and no free eta
map is constructed.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaComparisonReduction

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaValueGroupLineActual
open LeanFormal.IUT.NumberFieldFinitePlace
open IsDedekindDomain
open scoped NumberField

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual real line on the `Rss`/log-shell side of the comparison. -/
abbrev Rss : Type := ℝ

/-- The pilot sits over an actual selected native place. -/
theorem nativeFPlaceOverBad_mem_etaSelectedPlaces :
    nativeFPlaceOverBad X ∈ etaSelectedPlaces X :=
  by simp [etaSelectedPlaces, qPilotSelectedPlaces]

/-- Full eta comparison: the two eta maps agree on the whole actual Rval. -/
def EtaComparisonFull (etaQ etaAnab : Rval → Rss) : Prop :=
  ∀ a : Rval, etaQ a = etaAnab a

/-- Exact reduction: comparison only at the actual native q-pilot. -/
def EtaComparisonAtPilot (etaQ etaAnab : Rval → Rss) : Prop :=
  etaQ (etaPilot X) = etaAnab (etaPilot X)

/-- Actual one-way reduction: full eta comparison implies its pilot value. -/
theorem etaComparisonAtPilot_of_full
    {etaQ etaAnab : Rval → Rss}
    (h : EtaComparisonFull etaQ etaAnab) :
    EtaComparisonAtPilot (X := X) etaQ etaAnab :=
  h (etaPilot X)

/-- Exact missing eta source maps.  Both maps and their full comparison are
the ETA source obligation; no production construction is available. -/
structure EtaComparisonMaps (X : N8NativeInput l) where
  etaQ : Rval → Rss
  etaAnab : Rval → Rss
  comparison : EtaComparisonFull etaQ etaAnab

/-- The reduced comparison follows from the exact missing maps. -/
theorem etaComparisonAtPilot_of_maps
    (M : EtaComparisonMaps X) :
    EtaComparisonAtPilot (X := X) M.etaQ M.etaAnab :=
  etaComparisonAtPilot_of_full (X := X) M.comparison

end LeanFormal.IUT.N8Closure.EtaComparisonReduction