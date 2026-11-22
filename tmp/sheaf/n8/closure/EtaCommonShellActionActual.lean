import tmp.sheaf.n8.closure.EtaLogLinkCommonIntersection
import tmp.sheaf.n8.closure.EtaSourceActionLogLinkActual
import LeanFormal.IUT.IUTII.Kummer.VerticalLogKummerOrderedLayer

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaCommonShellActionActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaLogLinkCommonClosure
open LeanFormal.IUT.N8Closure.EtaLogLinkCommonIntersection
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open ABCBridge.N8.C3TensorTargetCorrection
open scoped Padic

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual unit group of the common algebraic closure. -/
abbrev AlgClUnits : Type := (AlgebraicClosure ℚ_[nativePrime X])ˣ

/-- Actual production log-link iterate on the algebraic-closure units, using
the root-system iteration (not field multiplication). -/
def sourceLogLinkIterate (m : Nat) : (n : Nat) → AlgClUnits X → AlgClUnits X
  | 0 => id
  | n + 1 => fun u =>
      rootSystemPowRoot (nativePrime X) (m + n + 1)
        (sourceLogLinkIterate m n u)

theorem sourceLogLinkIterate_zero (m : Nat) (u : AlgClUnits X) :
    sourceLogLinkIterate X m 0 u = u := rfl

theorem sourceLogLinkIterate_one (m : Nat) (u : AlgClUnits X) :
    sourceLogLinkIterate X m 1 u =
      rootSystemPowRoot (nativePrime X) (m + 1) u := by
  rfl

/-! ## Common shell units -/

/-- Units of the common closure whose underlying element lies in the actual
F-shell image; this is the unit part of `commonLayerShell`. -/
def commonShellUnits : Set (AlgClUnits X) :=
  {u | (u : PadicAlgCl (nativePrime X)) ∈ fShellImage X}

abbrev CommonShellUnit : Type :=
  {u : AlgClUnits X // u ∈ commonShellUnits X}

theorem commonShellUnit_mem (u : CommonShellUnit X) :
    (u.1 : PadicAlgCl (nativePrime X)) ∈ commonLayerShell X := by
  refine ⟨?_, u.2⟩
  exact ⟨u.1, rfl⟩

/-! ## Restricted action and compatibility targets -/

/-- Actual action map, before proving that it stays in the common shell. -/
def commonAction (m n : Nat) : AlgClUnits X → AlgClUnits X :=
  sourceLogLinkIterate X m n

/-- Exact compatibility/gap: the restricted action stays in the common shell. -/
def EtaCommonActionStaysInShell (m n : Nat) : Prop :=
  ∀ u : CommonShellUnit X,
    commonAction X m n u.1 ∈ commonShellUnits X

/-- Exact points that leave the intersection under the action. -/
def EtaCommonActionExitSet (m n : Nat) : Set (AlgClUnits X) :=
  {u | u ∈ commonShellUnits X ∧ commonAction X m n u ∉ commonShellUnits X}

/-- Exact readout compatibility target: action preserves membership in the
actual F-shell image (the shell readout side). -/
def EtaCommonActionShellReadoutCompatibility (m n : Nat) : Prop :=
  EtaCommonActionStaysInShell (X := X) m n

/-- Exact nonconstancy target: an actual common shell unit is moved. -/
def EtaCommonActionNonconstant (m n : Nat) : Prop :=
  ∃ u : CommonShellUnit X, commonAction X m n u.1 ≠ u.1

/-- Action law at zero: the restricted action is the identity map. -/
theorem commonAction_zero (m : Nat) (u : AlgClUnits X) :
    commonAction X m 0 u = u :=
  rfl

/-- The identity action stays trivially inside the shell. -/
theorem commonAction_staysInShell_zero (m : Nat) :
    EtaCommonActionStaysInShell (X := X) m 0 := by
  intro u
  simpa [commonAction, sourceLogLinkIterate] using u.2

end LeanFormal.IUT.N8Closure.EtaCommonShellActionActual
