import tmp.sheaf.xif.paper.S2214H1MonoidActual
import ContinuousKummerTheory.Kummer.Equiv
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2196ActionContinuousProofActual
open LeanFormal.IUT.XiFPaper.S2204ActualH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2214H1MonoidActual
open KummerTheory
namespace LeanFormal.IUT.XiFPaper.S2360KummerH1Actual
variable (p : Nat) [Fact (Nat.Prime p)] (n : ℕ)
local instance s2360NeZero : NeZero (Nat.factorial n) :=
  ⟨Nat.factorial_ne_zero n⟩
/-- Kummer theory at the actual local field: Q_p^x/(Q_p^x)^{n!} is the
external continuous H^1 of the absolute Galois group with mu_{n!}
coefficients. -/
noncomputable def S2360KummerEquiv :
    ℚ_[p]ˣ ⧸ (powMonoidHom (Nat.factorial n) : ℚ_[p]ˣ →* ℚ_[p]ˣ).range ≃*
      ContH1
        (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
        (Mu (Nat.factorial n) (AlgebraicClosure ℚ_[p])) :=
  KummerTheory.kummerEquivAlgClosure (Nat.factorial n) ℚ_[p]
/-- Exact first missing: comparison of the external Kummer H^1 with the
actual Iut.ContinuousH1 carrier S2204H1. -/
structure S2360H1Comparison where
  equiv : S2204H1 p n ≃
    ContH1
      (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (Mu (Nat.factorial n) (AlgebraicClosure ℚ_[p]))
/-- Exact first missing: finiteness of the actual H^1 level. -/
def S2360FiniteH1Required : Prop :=
  ∀ n, Finite (S2204H1 p n)
#check S2360KummerEquiv
#check S2360H1Comparison
#check S2360FiniteH1Required
end LeanFormal.IUT.XiFPaper.S2360KummerH1Actual
end
