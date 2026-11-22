import tmp.sheaf.n8.closure.EtaValueGroupLineActual
import tmp.sheaf.n8.closure.C2Native
import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogShellVolumeConsumer

/-!
# EtaRssLogShellLine

ETA-8b correction: the `Rss` carrier of the eta comparison is the actual
native log-shell/volume line, not the bare real line `ℝ`.

The carrier records the production native log-shell subset and the production
`LogShellVolumeConsumer` index, with the real log-volume coordinate derived
from that index.  The `Rss := ℝ` interface of `EtaComparisonReduction` is
replaced by this structure; a full comparison projects to the old real
coordinate only after the correction (one-way adapter), not by definition.

No free Real coordinate and no trivialized common line.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaRssLogShellLine

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C2Native
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaValueGroupLineActual
open LeanFormal.IUT.Foundations.LocalFields.LogShellVolume
open LeanFormal.IUT.NumberFieldFinitePlace
open IsDedekindDomain
open scoped NumberField

variable {l : PrimeGeFive} (X : N8NativeInput l)

local notation "Kbad" => CommonPrimeCompletion (K := X.S.arithmetic.Fmod)
  (C2Native.badPlaceAtPrime X)

/-- Actual `Rss` carrier: native log-shell subset plus the production volume
consumer index and its real log-volume coordinate. -/
structure EtaRssLogShellLineData (X : N8NativeInput l) where
  shell : Set (CommonPrimeCompletion (K := X.S.arithmetic.Fmod)
    (C2Native.badPlaceAtPrime X))
  shell_eq : shell = (C2Native.nativeLocalShell X).logShell
  volumeIndex : ℕ
  volumeIndex_eq : volumeIndex =
    (logShellVolumeConsumer (K := CommonPrimeCompletion (K := X.S.arithmetic.Fmod)
      (C2Native.badPlaceAtPrime X)) (p := (C2Native.badPrime X).val)).index
  logVolume : ℝ
  logVolume_eq : logVolume = Real.log (volumeIndex : ℝ)

/-- Actual construction from the production log-shell and consumer. -/
noncomputable def etaRssLogShellLineData : EtaRssLogShellLineData X where
  shell := (C2Native.nativeLocalShell X).logShell
  shell_eq := rfl
  volumeIndex :=
    (logShellVolumeConsumer (K := CommonPrimeCompletion (K := X.S.arithmetic.Fmod)
      (C2Native.badPlaceAtPrime X)) (p := (C2Native.badPrime X).val)).index
  volumeIndex_eq := rfl
  logVolume := Real.log
    ((logShellVolumeConsumer (K := CommonPrimeCompletion (K := X.S.arithmetic.Fmod)
      (C2Native.badPlaceAtPrime X)) (p := (C2Native.badPrime X).val)).index : ℝ)
  logVolume_eq := rfl

/-- Actual log-shell equals the production native shell, which production
identifies with `integralLogShell` (`C2Native.nativeLocalShell_logShell_eq`). -/
theorem etaRssLogShellLineData_shell_eq_nativeShell :
    (etaRssLogShellLineData X).shell = (C2Native.nativeLocalShell X).logShell :=
  (etaRssLogShellLineData X).shell_eq

/-- The actual real coordinate of an `Rss` point. -/
def EtaRssLogShellLineData.toReal (r : EtaRssLogShellLineData X) : ℝ :=
  r.logVolume

/-- Replacement of the old `Rss := ℝ` comparison: compare the actual log-shell
line, not a bare Real. -/
def EtaComparisonOnRss (etaQ etaAnab : Rval → EtaRssLogShellLineData X) : Prop :=
  ∀ a : Rval, etaQ a = etaAnab a

/-- One-way adapter to the old real-coordinate interface: actual `Rss`
comparison implies equality of the production log-volume coordinates. -/
theorem etaComparisonOnReal_of_rss
    {etaQ etaAnab : Rval → EtaRssLogShellLineData X}
    (h : EtaComparisonOnRss (X := X) etaQ etaAnab) :
    ∀ a : Rval, (etaQ a).toReal = (etaAnab a).toReal :=
  fun a => congrArg (fun r : EtaRssLogShellLineData X => r.toReal) (h a)

/-- Pilot-level replacement on the actual `Rss` line. -/
def EtaComparisonAtPilotOnRss
    (etaQ etaAnab : Rval → EtaRssLogShellLineData X) : Prop :=
  etaQ (etaPilot X) = etaAnab (etaPilot X)

theorem etaComparisonAtPilotOnRss_of_full
    {etaQ etaAnab : Rval → EtaRssLogShellLineData X}
    (h : EtaComparisonOnRss (X := X) etaQ etaAnab) :
    EtaComparisonAtPilotOnRss (X := X) etaQ etaAnab :=
  h (etaPilot X)

end LeanFormal.IUT.N8Closure.EtaRssLogShellLine