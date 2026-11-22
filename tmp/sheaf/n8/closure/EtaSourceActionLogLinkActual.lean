import LeanFormal.IUT.IUTII.Kummer.VerticalLogKummerOrderedLayer
import Mathlib

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaSourceActionLogLinkActual

open LeanFormal.IUT

variable (p : Nat) [Fact (Nat.Prime p)]

/-- The actual production log-link layer: the ordered vertical log-Kummer
layer on units of the algebraic closure, with `log m = rootSystemPowRoot p (m+1)`. -/
abbrev LogLinkLayer : VerticalLogKummerOrderedLayer :=
  unitLogKummerOrderedLayer p

/-- Actual one-step log-link on the layer. -/
def logLinkStep (m : Nat) : (LogLinkLayer p).F m → (LogLinkLayer p).F (m + 1) :=
  (LogLinkLayer p).log m

/-- Actual `n`-step log-link iteration (production `transport`). -/
def logLinkIterate (m n : Nat) : (LogLinkLayer p).F m → (LogLinkLayer p).F (m + n) :=
  (LogLinkLayer p).transport m n

/-- Actual set-level log-link action on a source region/packet.  This uses
the production `VerticalLogKummerCorrespondence.transport`, not field
multiplication on an additive carrier. -/
def logLinkSetAction (m n : Nat) (S : Set ((LogLinkLayer p).F m)) :
    Set ((LogLinkLayer p).F (m + n)) :=
  logLinkIterate p m n '' S

theorem logLinkSetAction_zero (m : Nat) (S : Set ((LogLinkLayer p).F m)) :
    logLinkSetAction p m 0 S = S := by
  simp [logLinkSetAction, logLinkIterate]

theorem logLinkSetAction_nonempty (m n : Nat)
    (S : Set ((LogLinkLayer p).F m)) (hS : S.Nonempty) :
    (logLinkSetAction p m n S).Nonempty :=
  hS.image (logLinkIterate p m n)

theorem logLinkSetAction_mono (m n : Nat)
    {S T : Set ((LogLinkLayer p).F m)} (hST : S ⊆ T) :
    logLinkSetAction p m n S ⊆ logLinkSetAction p m n T :=
  Set.image_mono hST

/-! ## Actual action package -/

/-- Actual log-link action package on the production ordered layer. -/
structure EtaSourceLogLinkAction where
  layer : VerticalLogKummerOrderedLayer
  layer_eq : layer = LogLinkLayer p
  step : (m : Nat) → layer.F m → layer.F (m + 1)
  step_eq : ∀ m, step m = layer.log m
  iterate : (m n : Nat) → layer.F m → layer.F (m + n)
  iterate_eq : ∀ m n, iterate m n = layer.transport m n
  action : (m n : Nat) → Set (layer.F m) → Set (layer.F (m + n))
  action_eq : ∀ m n S, action m n S = iterate m n '' S

noncomputable def etaSourceLogLinkAction : EtaSourceLogLinkAction p where
  layer := LogLinkLayer p
  layer_eq := rfl
  step := fun m => (LogLinkLayer p).log m
  step_eq := fun m => rfl
  iterate := fun m n => (LogLinkLayer p).transport m n
  iterate_eq := fun m n => rfl
  action := fun m n S => (LogLinkLayer p).transport m n '' S
  action_eq := fun m n S => rfl

theorem etaSourceLogLinkAction_nonempty :
    Nonempty (EtaSourceLogLinkAction p) :=
  ⟨etaSourceLogLinkAction p⟩

/-! ## Exact carrier gap -/

/- The production layer used here is the ordered `VerticalLogKummer` layer
on units of `AlgebraicClosure ℚ_[p]`.  There is no production map from the
actual F-place shell/packet carrier (`SourceLogShellDatum.logShell`) into
this layer's `F m`.  Such a shell-to-packet carrier bridge is the missing
declaration; no arbitrary transport is introduced here. -/
end LeanFormal.IUT.N8Closure.EtaSourceActionLogLinkActual
