import tmp.sheaf.n8.closure.EtaSourceActionLogLinkActual
import tmp.sheaf.n8.closure.EtaFPlaceNormalizedComparison

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaLogLinkToShellCarrier

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaSourceActionLogLinkActual
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison

universe u

variable {l : PrimeGeFive} (p : Nat) [Fact (Nat.Prime p)]
variable (X : N8NativeInput l)

/-- Actual log-link action data together with the actual F-place shell
carrier.  No map between them is asserted. -/
structure EtaLogLinkShellData (p : Nat) [Fact (Nat.Prime p)]
    (X : N8NativeInput l) where
  layer : EtaSourceLogLinkAction p
  layer_eq : layer = etaSourceLogLinkAction p
  shell : SourceLogShellDatum
  shell_eq : shell = fPlaceShell X

noncomputable def etaLogLinkShellData : EtaLogLinkShellData p X where
  layer := etaSourceLogLinkAction p
  layer_eq := rfl
  shell := fPlaceShell X
  shell_eq := rfl

theorem etaLogLinkShellData_nonempty :
    Nonempty (EtaLogLinkShellData p X) :=
  ⟨etaLogLinkShellData p X⟩

/-! ## Exact carrier bridge target -/

/- A carrier bridge would need an actual map from the production log-link
layer `F m = (AlgebraicClosure ℚ_[p])ˣ` to the F-place shell carrier
`SourceLogShellDatum.K` (or its `Units`), with image inside the shell.
No such production declaration exists.  This structure is the exact target
condition; it is not inhabited by an arbitrary map. -/
structure EtaLogLinkToShellBridge (p : Nat) [Fact (Nat.Prime p)]
    (X : N8NativeInput l) where
  layer : EtaSourceLogLinkAction p
  layer_eq : layer = etaSourceLogLinkAction p
  shell : SourceLogShellDatum
  shell_eq : shell = fPlaceShell X
  m : Nat
  carrierMap : (layer.layer.F m) → shell.K
  carrierMap_mem : ∀ u, carrierMap u ∈ shell.logShell

/-! ## Exact no-go statement -/

/- The missing declaration is precisely a source-compatible carrier map
from `unitLogKummerOrderedLayer p` units to the F-place `SourceLogShellDatum`
carrier (`K` or `Units`).  In particular, no field multiplication on the
additive `K` is used: the log-link side is the root-iteration layer, and the
shell side is `SourceLogShellDatum.logShell`. -/
def EtaLogLinkShellCarrierMapMissing : Prop :=
  ¬ Nonempty (EtaLogLinkToShellBridge p X)

end LeanFormal.IUT.N8Closure.EtaLogLinkToShellCarrier
