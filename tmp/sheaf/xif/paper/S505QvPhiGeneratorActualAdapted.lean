import tmp.sheaf.xif.paper.S480Example32InputActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import Iut.Foundations.SourceFiniteStageModelFrobenioid

/-! # S505: q_v generator on constant-N Phi and q_v tau submonoid

`Phi_{C_v^⊢} = N · log_Phi(q_v)` is the constant `N` submonoid of `Phi_{C_v}`.
At the abstract monoid level `N` is constant; the q_v content is the chosen
generator `logPhiQv` together with the q_v powers/tau.  This file constructs
the constant-N divisorial monoid at the actual qVFamily completion, the
chosen generator, and the q_v tau submonoid.  The mu_{2l}-orbit and the full
`CharacteristicSplitting` remain exact missing.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S505QvPhiGeneratorActualAdapted

open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S480Example32InputActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual qVFamily completion field. -/
abbrev QvK : Type := NumberFieldFinitePlace.Completion ((nativeBadLift T).lift b)

/-- The q_v order from the actual qVFamily candidate. -/
noncomputable def qOrder : ℕ := (qVFamily T b).order

theorem qOrder_pos : 0 < qOrder T b := (qVFamily T b).order_pos

/-- The q_v unit in the completion. -/
noncomputable def qvUnit : (QvK T b)ˣ :=
  Units.mk0 (qVFamily T b).q (qVFamily T b).q_ne_zero

/-- q_v powers submonoid (the tau candidate at the field level). -/
noncomputable def qvTauSubmonoid : Submonoid (QvK T b)ˣ where
  carrier := {x | ∃ n : ℤ, x = qvUnit T b ^ n}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro a b ⟨m, rfl⟩ ⟨n, rfl⟩
    exact ⟨m + n, by rw [zpow_add]⟩

/-- Constant-N Phi at the actual qVFamily completion. -/
noncomputable def qvPhi :
    DivisorialMonoidOn.{u+1} (Example32SmallBase (QvK T b))
      (fun {_ _} _ => True) :=
  example32PhiIsFSM (QvK T b)

/-- Chosen generator of `N · log_Phi(q_v)`: the monoid generator. -/
noncomputable def logPhiQv (X : Example32SmallBase (QvK T b)) :
    (qvPhi T b).obj X := ULift.up 1

/-- The chosen generator generates the constant monoid. -/
theorem logPhiQv_generator (X : Example32SmallBase (QvK T b))
    (y : (qvPhi T b).obj X) :
    ∃ n : ℕ, y = n • logPhiQv T b X := by
  rcases y with ⟨n⟩
  exact ⟨n, by simp [logPhiQv]⟩

end LeanFormal.IUT.XiFPaper.S505QvPhiGeneratorActualAdapted
end
