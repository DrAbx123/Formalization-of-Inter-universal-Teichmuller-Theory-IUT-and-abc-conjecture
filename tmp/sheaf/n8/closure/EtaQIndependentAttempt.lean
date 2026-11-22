import tmp.sheaf.n8.closure.C2Native
import tmp.sheaf.n8.closure.C9QPilotRegion
import tmp.sheaf.n8.closure.EtaRouteInterface

/-!
# Independent eta^q source attempt (ETA audit A)

Try to construct an actual q-side map
  native q-pilot unit -> shell units -> log-shell Rss
using the production logMap and unitNormLogDegree, independently of the
ScaleUp/ScaleDown negative control in EtaRouteInterface.

The q-pilot carrier is Completion (nativeFPlaceOverBad X).  The native shell is
C2Native.nativeLocalShell X, whose K is CommonPrimeCompletion
(badPlaceAtPrime X) (the Fmod-completion).  These are different completions.
Production has:
- qPilotSignedLog : Real (signed log, not an element of shell K),
- unitNormLogDegree : Multiplicative Real (not shell K),
- shell logMap : shell Units -> Multiplicative shell K,
but no map from the q-pilot units to shell Units.

No actual construction is available.  The exact named gap is the q-side map
EtaQSourceMap; no qPilotSignedLog sign is used as a substitute.

No Lean file is edited except this new file.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaQIndependentAttempt

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C2Native
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaRouteInterface
open LeanFormal.IUT.LocalFieldLogarithm

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual q-pilot carrier: the completion at the native F-place over the bad
base place. -/
abbrev NativeQCarrier (X : N8NativeInput l) : Type _ :=
  Completion (nativeFPlaceOverBad X)

/-- Actual q-pilot unit. -/
noncomputable def nativeQUnit (X : N8NativeInput l) : (NativeQCarrier X)ˣ :=
  Units.mk0 (C9QPilotRegion.nativeQ X).q (C9QPilotRegion.nativeQ X).q_ne_zero

/-- Actual q-pilot unit norm log degree (production value, Multiplicative Real). -/
noncomputable def nativeQLogDegree (X : N8NativeInput l) : Multiplicative ℝ :=
  unitNormLogDegree (NativeQCarrier X) (nativeQUnit X)

/-- The missing q-side map: q-pilot units map to shell units, and the shell
logMap image lies in the log-shell with nonzero value.  This is the exact
obligation type, not an assumed map in any destination structure. -/
structure EtaQSourceMap (X : N8NativeInput l) where
  /-- Missing actual q-unit to shell-unit map. -/
  qToShell : (NativeQCarrier X)ˣ →* (NativeShell X).Units
  /-- The image of the actual q unit under shell logMap lies in Rss. -/
  value_mem : ((NativeShell X).logMap (qToShell (nativeQUnit X))).toAdd ∈
    Rss X
  /-- The image is not the zero shell value. -/
  value_ne_zero : ((NativeShell X).logMap (qToShell (nativeQUnit X))).toAdd ≠ 0

/-- Exact q-side target: an actual EtaQSourceMap. -/
def EtaQIndependentTarget (X : N8NativeInput l) : Prop :=
  Nonempty (EtaQSourceMap X)

/-- The sign fact is recorded separately; it is not used as an eta^q map. -/
theorem nativeQ_sign_only (X : N8NativeInput l) : qPilotSignedLog X < 0 :=
  qPilotSignedLog_neg X

/-- The target does not accept the sign fact as a witness: its witness type
contains an actual qToShell map and a nonzero shell value, not a Real sign. -/
theorem etaQIndependentTarget_requires_map (X : N8NativeInput l)
    (h : EtaQIndependentTarget X) :
    ∃ _M : EtaQSourceMap X, True := by
  obtain ⟨M⟩ := h
  exact ⟨M, trivial⟩

end LeanFormal.IUT.N8Closure.EtaQIndependentAttempt
