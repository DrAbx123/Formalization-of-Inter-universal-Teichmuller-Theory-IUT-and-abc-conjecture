import tmp.sheaf.n8.closure.EtaRssLogShellLine
import tmp.sheaf.n8.closure.EtaIntegralStructureSourceBridge
import tmp.sheaf.n8.closure.EtaResidueMatchAttempt

/-!
# EtaRssSourceBridge

Attempt to attach the actual native log-shell `Rss` (`EtaRssLogShellLineData`,
built at the native bad completion) to the selected native place and the
integral structure S (`EtaIntegralStructureSourceBridge`).

Actual readouts on both sides are defined.  A full bridge would require the
base-residue match between S's `ℚ_[l.value]` and the selected native bad
completion; the production Clause B proves that match is false.  Therefore the
bridge with the exact source condition is empty (decisive no-go), and the
volume-index equality is recorded as the exact remaining gap.  No common Real
line and no arbitrary bridge is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaRssSourceBridgeRoute

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C2Native
open LeanFormal.IUT.N8Closure.EtaRssLogShellLine
open LeanFormal.IUT.N8Closure.EtaIntegralStructureSourceBridgeRoute
open LeanFormal.IUT.N8Closure.EtaResidueMatchAttempt
open LeanFormal.IUT.NumberFieldFinitePlace
open IsDedekindDomain
open scoped NumberField

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime l.value) := l.factPrime

/-- Actual native log-shell volume index readout. -/
def etaRssVolumeIndex : ℕ :=
  (etaRssLogShellLineData X).volumeIndex

/-- Actual S volume index readout at the selected native bridge. -/
def etaSourceVolumeIndex : ℕ :=
  etaVolumeIndex (etaIntegralStructureSourceBridge X)

/-- Exact remaining readout gap: equality of the native log-shell volume index
and S's selected volume index. -/
def EtaRssSourceVolumeIndexGap : Prop :=
  etaRssVolumeIndex X = etaSourceVolumeIndex X

/-- Full bridge with the exact source condition: the selected bad place must
have residue characteristic `l.value` (needed to match S's base `ℚ_[l.value]`). -/
structure EtaRssSourceBridge (X : N8NativeInput l) where
  rss : EtaRssLogShellLineData X
  rss_eq : rss = etaRssLogShellLineData X
  source : EtaIntegralStructureSourceBridge X
  source_eq : source = etaIntegralStructureSourceBridge X
  volumeIndex_eq : rss.volumeIndex = source.eta.volume.index
  residueMatch : EtaResidueMatchSourceCondition X

/-- Decisive no-go: the exact source condition is false by Clause B, so no
full `Rss`-to-S bridge exists. -/
theorem etaRssSourceBridge_isEmpty :
    IsEmpty (EtaRssSourceBridge X) :=
  ⟨fun B => etaResidueMatchSourceCondition_false X B.residueMatch⟩

end LeanFormal.IUT.N8Closure.EtaRssSourceBridgeRoute