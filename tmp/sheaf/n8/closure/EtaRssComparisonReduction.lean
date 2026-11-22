import tmp.sheaf.n8.closure.EtaRssLogShellLine
import tmp.sheaf.n8.closure.EtaComparisonReduction

/-!
# EtaRssComparisonReduction

ETA interface correction: the eta comparison is stated on the actual
log-shell/volume line `EtaRssLogShellLineData`, replacing the earlier bare
`Rss := ℝ` carrier of `EtaComparisonReduction`.

The full comparison is exact equality of the two eta maps into the actual
log-shell line; it reduces one-way to the pilot and to the production
log-volume coordinate.  The eta maps themselves remain the exact missing ETA
source object (named gap).  No common real line is used as the carrier.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaRssComparisonReduction

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaValueGroupLineActual
open LeanFormal.IUT.N8Closure.EtaRssLogShellLine
open LeanFormal.IUT.NumberFieldFinitePlace
open IsDedekindDomain
open scoped NumberField

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Full comparison on the actual log-shell `Rss`: the two eta maps agree on
the whole actual `Rval`. -/
def EtaLogShellComparisonFull
    (etaQ etaAnab : Rval → EtaRssLogShellLineData X) : Prop :=
  ∀ a : Rval, etaQ a = etaAnab a

/-- Pilot-level comparison on the actual log-shell `Rss`. -/
def EtaLogShellComparisonAtPilot
    (etaQ etaAnab : Rval → EtaRssLogShellLineData X) : Prop :=
  etaQ (etaPilot X) = etaAnab (etaPilot X)

/-- Actual one-way reduction: full log-shell comparison implies pilot equality. -/
theorem etaLogShellComparisonAtPilot_of_full
    {etaQ etaAnab : Rval → EtaRssLogShellLineData X}
    (h : EtaLogShellComparisonFull (X := X) etaQ etaAnab) :
    EtaLogShellComparisonAtPilot (X := X) etaQ etaAnab :=
  h (etaPilot X)

/-- Actual one-way adapter to the production log-volume coordinate. -/
theorem etaLogShellComparisonOnReal_of_full
    {etaQ etaAnab : Rval → EtaRssLogShellLineData X}
    (h : EtaLogShellComparisonFull (X := X) etaQ etaAnab) :
    ∀ a : Rval, (etaQ a).toReal = (etaAnab a).toReal :=
  fun a => congrArg (fun r : EtaRssLogShellLineData X => r.toReal) (h a)

/-- Exact missing eta maps into the actual log-shell `Rss`. -/
structure EtaLogShellComparisonMaps (X : N8NativeInput l) where
  etaQ : Rval → EtaRssLogShellLineData X
  etaAnab : Rval → EtaRssLogShellLineData X
  comparison : EtaLogShellComparisonFull (X := X) etaQ etaAnab

theorem etaLogShellComparisonAtPilot_of_maps
    (M : EtaLogShellComparisonMaps X) :
    EtaLogShellComparisonAtPilot (X := X) M.etaQ M.etaAnab :=
  etaLogShellComparisonAtPilot_of_full (X := X) M.comparison

end LeanFormal.IUT.N8Closure.EtaRssComparisonReduction