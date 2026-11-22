import tmp.sheaf.xif.paper.S2372KummerFiniteActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
open LeanFormal.IUT
open KummerTheory
open LeanFormal.IUT.XiFPaper.S2196ActionContinuousProofActual
open LeanFormal.IUT.XiFPaper.S2204ActualH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2360KummerH1Actual
open LeanFormal.IUT.XiFPaper.S2372KummerFiniteActual
namespace LeanFormal.IUT.XiFPaper.S2384H1ComparisonActual
variable (p : Nat) [Fact (Nat.Prime p)] (n : ℕ)
local instance s2384NeZero : NeZero (Nat.factorial n) :=
  ⟨Nat.factorial_ne_zero n⟩
/-- The external continuous H^1 of the local absolute Galois group with
mu_{n!} coefficients. -/
noncomputable abbrev S2384ExternalH1 : Type :=
  ContH1 Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])
    (Mu (Nat.factorial n) (AlgebraicClosure ℚ_[p]))
/-- Kummer theory plus the finite Kummer quotient gives finiteness of the
external H^1. -/
theorem S2384ExternalH1_finite :
    Finite (S2384ExternalH1 p n) := by
  haveI : Finite (S2372KummerQuotient p n) :=
    S2372KummerQuotient_finite p n
  exact Finite.of_injective
    (fun x : S2384ExternalH1 p n =>
      (S2360KummerEquiv p n).symm x)
    (S2360KummerEquiv p n).symm.injective
/-- Exact first missing: the comparison of the internal Iut.ContinuousH1
with the external ContH1. -/
structure S2384H1Comparison where
  equiv : S2204H1 p n ≃ S2384ExternalH1 p n
/-- Given the comparison, finiteness transfers to the actual H^1 carrier. -/
theorem S2384FiniteH1OfComparison
    (D : S2384H1Comparison p n) :
    Finite (S2204H1 p n) := by
  haveI : Finite (S2384ExternalH1 p n) := S2384ExternalH1_finite p n
  exact Finite.of_injective (fun x : S2204H1 p n => D.equiv x)
    D.equiv.injective
#check S2384ExternalH1
#check S2384ExternalH1_finite
#check S2384H1Comparison
#check S2384FiniteH1OfComparison
end LeanFormal.IUT.XiFPaper.S2384H1ComparisonActual
end
