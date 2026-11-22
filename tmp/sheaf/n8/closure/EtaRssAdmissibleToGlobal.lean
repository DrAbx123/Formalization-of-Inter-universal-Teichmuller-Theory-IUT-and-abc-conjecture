import tmp.sheaf.n8.closure.EtaRssAdmissibleCorrection
import tmp.sheaf.n8.closure.EtaRegionAdmVariation
import Mathlib

/-!
# Local admissible Rss to global VaryingRegionRss: exact carrier bridge target

The local zero-sorry admissible Rss is over the F-completion
CommonPrimeCompletion (K := F) nativeFPlaceAtPrime.  The global
RegionAdmVariation/VaryingRegionRss uses localFieldAt X (badPlace X), the
completion at the selected bad native K-place.  No production ring comparison
between these carriers is present, so the local-to-global class map is not
constructed by an arbitrary transport.  The exact missing bridge is recorded
below as a named source gap.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaAnabAtFPlace
open LeanFormal.IUT.N8Closure.EtaRssAdmissibleCorrection
open LeanFormal.IUT.N8Closure.EtaRegionAdmVariation

namespace LeanFormal.IUT.N8Closure.EtaRssAdmissibleToGlobal

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [Field (localFieldAt X (badPlace X))]

abbrev LocalCarrier : Type := K X
abbrev GlobalBadCarrier : Type := localFieldAt X (badPlace X)

/-- Exact carrier bridge target: actual ring equivalence between the local
F-completion and the global bad-place K-completion. -/
def LocalGlobalCarrierBridge : Prop :=
  Nonempty (LocalCarrier X ≃+* GlobalBadCarrier X)

/-! ## Exact no-go for a direct class map

A local admissible class lives in the F-completion quotient.  A global
VaryingRegionRss class is a GlobalRegion X modulo equality of the mass at
badPlace X, whose local field is the K-completion.  Without a production
carrier comparison, any region/class transport would be arbitrary.  Hence the
bridge target above is the exact gap; no singleton or arbitrary region is used.
-/

end LeanFormal.IUT.N8Closure.EtaRssAdmissibleToGlobal
