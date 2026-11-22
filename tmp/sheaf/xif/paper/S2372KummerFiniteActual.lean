import tmp.sheaf.xif.paper.S2360KummerH1Actual
import PadicField.PowIndexPadic
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2360KummerH1Actual
namespace LeanFormal.IUT.XiFPaper.S2372KummerFiniteActual
variable (p : Nat) [Fact (Nat.Prime p)] (n : ℕ)
local instance s2372NeZero : NeZero (Nat.factorial n) :=
  ⟨Nat.factorial_ne_zero n⟩
/-- The Kummer quotient Q_p^x/(Q_p^x)^{n!}. -/
noncomputable abbrev S2372KummerQuotient : Type :=
  ℚ_[p]ˣ ⧸ (powMonoidHom (Nat.factorial n) :
    ℚ_[p]ˣ →* ℚ_[p]ˣ).range
/-- The Kummer quotient is finite, from the padic index formula. -/
theorem S2372KummerQuotient_finite :
    Finite (S2372KummerQuotient p n) := by
  classical
  let H : Subgroup ℚ_[p]ˣ :=
    (powMonoidHom (Nat.factorial n) :
      ℚ_[p]ˣ →* ℚ_[p]ˣ).range
  have hindex : H.index =
      Nat.factorial n * Nat.card
        (rootsOfUnity (Nat.factorial n) ℚ_[p]) *
        p ^ (padicValNat p (Nat.factorial n) *
          Module.finrank ℚ_[p] ℚ_[p]) :=
    PadicField.index_range_pow
      (p := p) (K := ℚ_[p]) (n := Nat.factorial n)
  haveI : Nonempty (rootsOfUnity (Nat.factorial n) ℚ_[p]) := ⟨1⟩
  have hcard : Nat.card (rootsOfUnity (Nat.factorial n) ℚ_[p]) ≠ 0 :=
    (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩)
  have hne : H.index ≠ 0 := by
    rw [hindex, mul_assoc]
    apply Nat.mul_ne_zero
    · exact Nat.factorial_ne_zero n
    · exact Nat.mul_ne_zero hcard
        (pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero)
  haveI : H.FiniteIndex := Subgroup.finiteIndex_iff.mpr hne
  haveI : Fintype (ℚ_[p]ˣ ⧸ H) := H.fintypeQuotientOfFiniteIndex
  exact Finite.of_fintype _
/-- Exact first missing: the comparison between external ContH1 and the
actual Iut.ContinuousH1 carrier. -/
abbrev S2372H1ComparisonRequired : Type :=
  S2360H1Comparison p n
#check S2372KummerQuotient
#check S2372KummerQuotient_finite
#check S2372H1ComparisonRequired
end LeanFormal.IUT.XiFPaper.S2372KummerFiniteActual
end
