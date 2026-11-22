import LeanFormal.IUT.ABCBridge.Bridge.ABCEllipticHeightCriterion
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary
import tmp.sheaf.xif.paper.Mzk1G1CriterionAllActual
import tmp.sheaf.xif.paper.Mzk1G1EllipticHeightCriterionActual
import tmp.sheaf.xif.paper.ABCStatementBridgeActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.ABCStatementBridgeActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P8ABCFromPointFinal
def P8PointHeightCriterion : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + ε) * Real.log (radical (a * b * c) : ℝ) + B
def p8_freyHeightBound (h : P8PointHeightCriterion) :
    ∀ ε : ℝ, 0 < ε → FreyHeightBound ε := by
  intro ε hε
  let B := Classical.choose (h ε hε)
  have hB := Classical.choose_spec (h ε hε)
  refine { C := Real.exp B, C_nonneg := le_of_lt (Real.exp_pos B), height_ineq := ?_ }
  intro a b c ha hb hc hab hcop
  have htriple : IsABCTriple a b c := ⟨ha, hb, hab, by
    intro p hp hpa hpb
    exact hcop (Nat.dvd_mul_of_dvd_left hp hpa) (Nat.dvd_mul_of_dvd_left hp hpb)⟩
  have hp := hB a b c htriple
  have hpos : (0 : ℝ) < (radical (a * b * c) : ℝ) := by exact_mod_cast radical_pos (a * b * c)
  have hlog : Real.log (c : ℝ) ≤ (1 + ε) * Real.log (radical (a * b * c) : ℝ) + B := by
    rwa [← abcRationalPoint_logHeight₁ htriple]
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have h1 : (c : ℝ) ≤ Real.exp ((1 + ε) * Real.log (radical (a * b * c) : ℝ) + B) :=
    (Real.log_le_iff_le_exp hcpos).mp hlog
  have h2 : Real.exp ((1 + ε) * Real.log (radical (a * b * c) : ℝ) + B) =
      Real.exp B * (radical (a * b * c) : ℝ) ^ (1 + ε) := by
    rw [Real.exp_add, Real.exp_mul, Real.exp_log hpos]
  rw [h2] at h1
  simpa [freyConductor] using h1
def p8_criterionAll (h : P8PointHeightCriterion) : ABCEllipticHeightCriterionAll :=
  criterionAll_of_freyHeight (p8_freyHeightBound h)
theorem p8_abcStatement (h : P8PointHeightCriterion) : ABCStatement :=
  abcStatement_of_ellipticHeightCriterion (p8_criterionAll h)
theorem p8_abcConjecture (h : P8PointHeightCriterion) : ABCConjecture :=
  abcStatement_iff_ABCConjecture.mp (p8_abcStatement h)
#print axioms p8_abcConjecture
end LeanFormal.IUT.XiFPaper.Mzk1P8ABCFromPointFinal
end