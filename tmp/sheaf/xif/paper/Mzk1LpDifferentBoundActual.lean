/- G-K (route §7.2 step 3): the actual local different upper bound for finite
extensions of `Q_p`, transported from the repository donor
`LeanFormal/IUT/Foundations/LocalFields/LocalDifferentUpperBound` (IUT IV Prop
1.3(ii)), together with the bounded-degree corollary used in route §7.2
steps 3-4 (uniform separation of conjugates).

This file only imports and composes the actual donor theorem; the donor's
oleans are present (`.lake/build/lib/lean/LeanFormal/IUT/Foundations/LocalFields/LocalDifferentUpperBound.olean`),
so importing it is the intended "transport" route of §7.2 step 3. -/
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentUpperBound
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1LpDifferentBoundActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalDifferentUpperBound
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.IntegralTraceDualTensorInclusion

variable {p : ℕ} [Fact p.Prime]

/-- **Actual donor bound** (IUT IV Prop 1.3(ii), repository form): for a tower of
finite `Q_p`-extensions `K ⊆ L`,

`ord_p(different_{L/Q_p}) ≤ ord_p(different_{K/Q_p}) + v_p([L:K]) + 1/e(K)`. -/
theorem localDifferentPaperOrder_le_degree_padicVal'
    {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
    [IsUltrametricDist K] [ProperSpace K] [NormedAlgebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K]
    {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L]
    [IsUltrametricDist L] [ProperSpace L] [NormedAlgebra ℚ_[p] L]
    [FiniteDimensional ℚ_[p] L] [NormedAlgebra K L] [IsScalarTower ℚ_[p] K L] :
    localDifferentPaperOrder (p := p) (L := L) ≤
      localDifferentPaperOrder (p := p) (L := K) +
        padicValNat p (Module.finrank K L) +
        1 / (logShellRamificationExponent (K := K) (p := p) : ℝ) :=
  localDifferentPaperOrder_le_degree_padicVal

/-- **Bounded-degree different corollary** (route §7.2 step 3): if `[L:K] ≤ d`, the
actual different order of `L` is bounded by `ord_p(different_{K/Q_p}) + log_p(d) + 1/e(K)`. -/
theorem localDifferentPaperOrder_le_boundedDegree
    {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
    [IsUltrametricDist K] [ProperSpace K] [NormedAlgebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K]
    {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L]
    [IsUltrametricDist L] [ProperSpace L] [NormedAlgebra ℚ_[p] L]
    [FiniteDimensional ℚ_[p] L] [NormedAlgebra K L] [IsScalarTower ℚ_[p] K L]
    (d : ℕ) (hd : Module.finrank K L ≤ d) :
    localDifferentPaperOrder (p := p) (L := L) ≤
      localDifferentPaperOrder (p := p) (L := K) +
        (Nat.log p d : ℝ) +
        1 / (logShellRamificationExponent (K := K) (p := p) : ℝ) := by
  refine (localDifferentPaperOrder_le_degree_padicVal' (p := p) (K := K) (L := L)).trans ?_
  have hval : (padicValNat p (Module.finrank K L) : ℝ) ≤ (Nat.log p d : ℝ) := by
    have h := padicValNat_le_nat_log (p := p) (Module.finrank K L)
    have hd' : Nat.log p (Module.finrank K L) ≤ Nat.log p d := Nat.log_mono_right hd
    exact_mod_cast h.trans hd'
  linarith

/-- **Normalisation dictionary**: `localDifferentPaperOrder` is the
field-valuation different (`δ/e`); hence the `ord_p`-normalised different order is
`localDifferentOrder = localDifferentPaperOrder * e`. -/
theorem localDifferentOrder_eq_paperOrder_mul_ramification
    {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
    [IsUltrametricDist K] [ProperSpace K] [NormedAlgebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] :
    (localDifferentOrder (p := p) (L := K) : ℝ) =
      localDifferentPaperOrder (p := p) (L := K) *
        (logShellRamificationExponent (K := K) (p := p) : ℝ) := by
  unfold localDifferentPaperOrder
  have he : (logShellRamificationExponent (K := K) (p := p) : ℝ) ≠ 0 := by
    exact_mod_cast (logShellRamificationExponent_pos (K := K) (p := p)).ne'
  field_simp

#print axioms localDifferentPaperOrder_le_degree_padicVal'
#print axioms localDifferentPaperOrder_le_boundedDegree
#print axioms localDifferentOrder_eq_paperOrder_mul_ramification

end LeanFormal.IUT.XiFPaper.Mzk1LpDifferentBoundActual
end