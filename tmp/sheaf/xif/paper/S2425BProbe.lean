import tmp.sheaf.xif.paper.S2419H1SurjLimitActual
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
namespace LeanFormal.IUT.XiFPaper.S2425BProbe
theorem S2425FactDvd (n : Nat) :
    Nat.factorial n ∣ Nat.factorial (n+1) :=
  Nat.factorial_dvd_factorial (Nat.le_succ n)
theorem S2425FactDiv (n : Nat) :
    Nat.factorial (n+1) / Nat.factorial n = n+1 := by
  rw [Nat.factorial_succ]
  exact Nat.mul_div_left (n+1) (Nat.factorial_pos n)
variable (p : Nat) [Fact (Nat.Prime p)] (n : ℕ)
example (ζ : S2145Coeff p (n+1)) :
    KummerTheory.Mu.transition (S2425FactDvd n) ζ = S2145PowMap p n ζ := by
  apply Subtype.ext
  change ζ.1 ^ (Nat.factorial (n+1) / Nat.factorial n) = ζ.1 ^ (n+1)
  rw [S2425FactDiv]
end LeanFormal.IUT.XiFPaper.S2425BProbe
end
