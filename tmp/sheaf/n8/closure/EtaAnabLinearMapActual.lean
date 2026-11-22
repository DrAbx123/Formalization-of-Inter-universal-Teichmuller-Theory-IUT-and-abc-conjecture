import tmp.sheaf.n8.closure.EtaAnabFromShellRegions
import tmp.sheaf.n8.closure.EtaValueGroupLineActual
import tmp.sheaf.n8.closure.EtaAnabToVaryingRss
import Mathlib

/-!
# etaAnab linear map Rval -> varying Rss: exact source-action gap

The actual F-shell region and its varying-Rss class are constructed in
EtaAnabFromShellRegions.

A nonconstant linear map Rval -> Rss would need an actual action of the
multiplicative real line Rval on K-regions (Kummer/log-shell or q powers).  The
only actual scalars on the p-adic completion K are in K* / Q_p*: q powers give
at most a Z-indexed family q^n . region.  There is no actual R-action on K and
no production theorem that the q^n-scaled regions have distinct varying-Rss
classes.  Extending a Z-family to Rval would be arbitrary.

This file records the exact missing source action; no if/arbitrary map is used.
-/

noncomputable section

namespace ABCBridge.N8.EtaAnabLinearMapActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open ABCBridge.N8.EtaAnabFromShellRegions
open LeanFormal.IUT.N8Closure.EtaValueGroupLineActual
open LeanFormal.IUT.N8Closure.EtaRssNontrivialActual
open ABCBridge.N8.EtaAnabToVaryingRss

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance fPlaceMeasurableSpace (X : N8NativeInput l) : MeasurableSpace (FPlaceK X) :=
  borel (FPlaceK X)

local instance fPlaceBorelSpace (X : N8NativeInput l) : BorelSpace (FPlaceK X) :=
  ⟨rfl⟩

/-- A nonconstant linear map on the actual value-group line to the actual
varying Rss, tied to the actual F-shell class. -/
structure EtaAnabLinearMapActual where
  map : Rval → Rss (K := FPlaceK X) (fPlaceMeasure X)
  map_one : map 1 = fPlaceShellClass (X := X)
  nonconstant : ∃ a b : Rval, map a ≠ map b

/-- Exact missing source action: an actual Rval-action on F-place regions whose
orbit classes are nonconstant.  This is the object a q-power construction would
have to supply; it is not an arbitrary function. -/
structure EtaAnabRvalRegionAction where
  act : Rval → PositiveFiniteRegion (FPlaceK X) (fPlaceMeasure X)
  act_one : act 1 = fPlaceShellRegion (X := X)
  nonconstant : ∃ a b : Rval,
    regionClass (K := FPlaceK X) (mu := fPlaceMeasure X) (act a) ≠
      regionClass (K := FPlaceK X) (mu := fPlaceMeasure X) (act b)

/-- Conditional construction: an actual Rval-region action gives the linear map
to varying Rss, zero sorry. -/
noncomputable def etaAnabLinearMapActualOfRegionAction
    (A : EtaAnabRvalRegionAction (X := X)) : EtaAnabLinearMapActual (X := X) where
  map := fun a => regionClass (K := FPlaceK X) (mu := fPlaceMeasure X) (A.act a)
  map_one := by
    rw [A.act_one]
    rfl
  nonconstant := by
    obtain ⟨a, b, h⟩ := A.nonconstant
    exact ⟨a, b, h⟩

/-- The exact gap: no production Rval-region action on the actual F-place
completion is available.  q powers only give a Z-indexed family and no
nonconstancy/Haar-scaling theorem for the varying-Rss classes. -/
def EtaAnabRvalRegionActionGap : Prop :=
  Nonempty (EtaAnabRvalRegionAction (X := X))

end ABCBridge.N8.EtaAnabLinearMapActual
