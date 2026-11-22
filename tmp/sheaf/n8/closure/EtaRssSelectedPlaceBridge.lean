import tmp.sheaf.n8.closure.EtaRssLogShellLine
import tmp.sheaf.n8.closure.EtaIntegralStructureAtSelectedPlace

/-!
# EtaRssSelectedPlaceBridge

Correction after the Q_l residue no-go: attach the actual native log-shell
`Rss` (`EtaRssLogShellLineData`) to the corrected integral structure S at the
selected bad native place (`EtaIntegralStructureAtSelectedPlace`), not to the
wrong Q_[l.value] S.

Both `Rss` and the corrected S use the selected bad base place's completion
`CommonPrimeCompletion (badBasePlace X, completionRationalPrime ...)`, so the
volume-index equality is actual (definitional).  No common Real line and no
old Q_l S is used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaRssSelectedPlaceBridgeRoute

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C2Native
open LeanFormal.IUT.N8Closure.EtaRssLogShellLine
open LeanFormal.IUT.N8Closure.EtaIntegralStructureAtSelectedPlaceRoute
open LeanFormal.IUT.NumberFieldFinitePlace
open IsDedekindDomain
open scoped NumberField

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual selected-place S volume index. -/
def etaSelectedVolumeIndex : ℕ :=
  (etaIntegralStructureAtSelectedPlace X).volume.index

/-- Actual equality: the native log-shell volume index is the selected-place
S volume index. -/
theorem etaRssVolumeIndex_eq_selectedVolumeIndex :
    (etaRssLogShellLineData X).volumeIndex = etaSelectedVolumeIndex X :=
  rfl

/-- Actual bridge from the log-shell `Rss` to the selected-place S. -/
structure EtaRssSelectedPlaceBridge (X : N8NativeInput l) where
  rss : EtaRssLogShellLineData X
  rss_eq : rss = etaRssLogShellLineData X
  selected : EtaIntegralStructureAtSelectedPlace X
  selected_eq : selected = etaIntegralStructureAtSelectedPlace X
  volumeIndex_eq : rss.volumeIndex = selected.volume.index

noncomputable def etaRssSelectedPlaceBridge :
    EtaRssSelectedPlaceBridge X where
  rss := etaRssLogShellLineData X
  rss_eq := rfl
  selected := etaIntegralStructureAtSelectedPlace X
  selected_eq := rfl
  volumeIndex_eq := rfl

theorem etaRssSelectedPlaceBridge_nonempty :
    Nonempty (EtaRssSelectedPlaceBridge X) :=
  ⟨etaRssSelectedPlaceBridge X⟩

end LeanFormal.IUT.N8Closure.EtaRssSelectedPlaceBridgeRoute