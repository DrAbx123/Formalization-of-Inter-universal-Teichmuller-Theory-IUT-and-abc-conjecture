import tmp.sheaf.xif.paper.Mzk1P8PointHeightCriterionActual
import tmp.sheaf.xif.paper.Mzk1G1CriterionAllActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P8PointHeightCriterionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
namespace LeanFormal.IUT.XiFPaper.Mzk1P8FreyHeightFromPointActual
def p8_freyHeightBound_of_pointCriterion
    (h : P8PointHeightCriterion) :
    ∀ ε : ℝ, 0 < ε → FreyHeightBound ε := by
  intro ε hε
  let B := Classical.choose (h ε hε)
  have hB := Classical.choose_spec (h ε hε)
  refine
    { C := Real.exp B
      C_nonneg := le_of_lt (Real.exp_pos B)
      height_ineq := ?_ }
  intro a b c ha hb hc hab hcop
  have htriple : IsABCTriple a b c := ⟨ha, hb, hc, hab, by
    intro p hp hpa hpb
    exact hcop (Nat.dvd_mul_of_dvd_left hp hpa) (Nat.dvd_mul_of_dvd_left hp hpb)⟩
  have hp := hB a b c htriple
  have hpos : (0 : ℝ) < (radical (a * b * c) : ℝ) := by
    exact_mod_cast radical_pos (a * b * c)
  have hlog : Real.log (c : ℝ) ≤ (1 + ε) * Real.log (radical (a * b * c) : ℝ) + B := by
    rwa [← abcRationalPoint_logHeight₁ htriple]
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have h1 : (c : ℝ) ≤ Real.exp ((1 + ε) * Real.log (radical (a * b * c) : ℝ) + B) :=
    (Real.log_le_iff_le_exp hcpos).mp hlog
  have h2 : Real.exp ((1 + ε) * Real.log (radical (a * b * c) : ℝ) + B) =
      Real.exp B * (radical (a * b * c) : ℝ) ^ (1 + ε) := by
    rw [Real.exp_add, Real.exp_mul, Real.exp_log hpos]
  rw [h2] at h1
  exact h1
#print axioms p8_freyHeightBound_of_pointCriterion
end LeanFormal.IUT.XiFPaper.Mzk1P8FreyHeightFromPointActual
end