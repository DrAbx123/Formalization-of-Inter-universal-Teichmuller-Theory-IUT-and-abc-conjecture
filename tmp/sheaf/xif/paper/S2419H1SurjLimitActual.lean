import tmp.sheaf.xif.paper.S2410H1EquivDoneActual
import ContinuousKummerTheory.Kummer.Limit
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
open LeanFormal.IUT
open KummerTheory
open LeanFormal.IUT.XiFPaper.S2145MuH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2196ActionContinuousProofActual
open LeanFormal.IUT.XiFPaper.S2204ActualH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2214H1MonoidActual
open LeanFormal.IUT.XiFPaper.S2410H1EquivDoneActual
namespace LeanFormal.IUT.XiFPaper.S2419H1SurjLimitActual
variable (p : Nat) [Fact (Nat.Prime p)]
/-- The quotient transition on Kummer quotients is surjective. -/
theorem S2419QuotTransition_surjective {m n : ℕ} (h : m ∣ n) :
    Function.Surjective
      (KummerTheory.quotTransition (K := ℚ_[p]) h) := by
  intro x
  induction x using QuotientGroup.induction_on with
  | H a =>
      exact ⟨QuotientGroup.mk a, rfl⟩
/-- The external Kummer H^1 transition is surjective. -/
theorem S2419H1Transition_surjective (m n : ℕ)
    [NeZero (m : ℚ_[p])] [NeZero (n : ℚ_[p])] (h : m ∣ n) :
    Function.Surjective
      (KummerTheory.h1Transition (K := ℚ_[p])
        (Ω := AlgebraicClosure ℚ_[p]) h) := by
  intro y
  obtain ⟨x, rfl⟩ :=
    (KummerTheory.kummerEquiv m ℚ_[p]
      (AlgebraicClosure ℚ_[p])).surjective y
  obtain ⟨x0, hx0⟩ := S2419QuotTransition_surjective p h x
  refine ⟨(KummerTheory.kummerEquiv n ℚ_[p]
    (AlgebraicClosure ℚ_[p])) x0, ?_⟩
  rw [KummerTheory.kummerEquiv_quotTransition h x0, hx0]
/-- Exact missing: surjectivity of the internal level transition. -/
def S2419H1SurjectiveRequired : Prop :=
  ∀ n, Function.Surjective (⇑(S2214H1PushforwardHom p n))
#check S2419QuotTransition_surjective
#check S2419H1SurjectiveRequired
end LeanFormal.IUT.XiFPaper.S2419H1SurjLimitActual
end
