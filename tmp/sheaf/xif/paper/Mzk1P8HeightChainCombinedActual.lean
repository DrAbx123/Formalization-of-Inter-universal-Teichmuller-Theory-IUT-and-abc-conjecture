import LeanFormal.IUT.ABCBridge.Geometry.ABCModelHeightComparison
import LeanFormal.IUT.ABCBridge.Bridge.ABCEllipticHeightCriterion
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary
import tmp.sheaf.xif.paper.Mzk1G1CriterionAllActual
import tmp.sheaf.xif.paper.Mzk1G1EllipticHeightCriterionActual
import tmp.sheaf.xif.paper.ABCStatementBridgeActual
import tmp.sheaf.xif.paper.Mzk1P6PaperBoundActual
import tmp.sheaf.xif.paper.Mzk1P8ActualDisplayHeightActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.Mzk1P6PaperBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual
open LeanFormal.IUT.XiFPaper.ABCStatementBridgeActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P8HeightChainCombinedActual
def P8PointHeightCriterion : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + ε) * Real.log (radical (a * b * c) : ℝ) + B
theorem p8_pointHeightCriterion_iff_freyJ :
    P8PointHeightCriterion ↔ ABCFreyJProductHeightCriterion := by
  constructor
  · intro h ε hε
    let B := Classical.choose (h ε hε)
    have hB := Classical.choose_spec (h ε hε)
    refine ⟨6 * B + Real.log 256, ?_⟩
    intro a b c habc
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple habc
    have hp := hB a b c habc
    have hj := (rationalFreyWeierstrassCurve_height_upper_bound_transfers habc
      ((1 + ε) * Real.log (radical (a * b * c) : ℝ) + B)).2.2.2 hp
    nlinarith
  · intro h ε hε
    let B := Classical.choose (h ε hε)
    have hB := Classical.choose_spec (h ε hε)
    refine ⟨(B - Real.log (27 / 64 : ℝ)) / 6, ?_⟩
    intro a b c habc
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple habc
    have hj := hB a b c habc
    have hp := (rationalFreyWeierstrassCurve_height_upper_bound_transfers habc
      (6 * (1 + ε) * Real.log (radical (a * b * c) : ℝ) + B)).2.2.1
      (by nlinarith [hj])
    nlinarith
def p8_freyHeightBound_of_pointCriterion (h : P8PointHeightCriterion) :
    ∀ ε : ℝ, 0 < ε → FreyHeightBound ε := by
  intro ε hε
  let B := Classical.choose (h ε hε)
  have hB := Classical.choose_spec (h ε hε)
  refine { C := Real.exp B, C_nonneg := le_of_lt (Real.exp_pos B), height_ineq := ?_ }
  intro a b c ha hb hc hab hcop
  have htriple : IsABCTriple a b c := ⟨ha, hb, hc, hab, by
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
  rwa [h2] at h1
def p8_criterionAll_of_pointCriterion (h : P8PointHeightCriterion) :
    ABCEllipticHeightCriterionAll :=
  criterionAll_of_freyHeight (p8_freyHeightBound_of_pointCriterion h)
theorem p8_abcStatement_of_pointCriterion (h : P8PointHeightCriterion) : ABCStatement :=
  abcStatement_of_ellipticHeightCriterion (p8_criterionAll_of_pointCriterion h)
theorem p8_abcConjecture_of_pointCriterion (h : P8PointHeightCriterion) : ABCConjecture :=
  abcStatement_iff_ABCConjecture.mp (p8_abcStatement_of_pointCriterion h)
theorem p8_uniformHeightBound_of_pointCriterion (h : P8PointHeightCriterion) :
    P8UniformHeightBound :=
  p8_pointHeightCriterion_iff_freyJ.mp h
#print axioms p8_pointHeightCriterion_iff_freyJ
#print axioms p8_abcConjecture_of_pointCriterion
#print axioms p8_uniformHeightBound_of_pointCriterion
end LeanFormal.IUT.XiFPaper.Mzk1P8HeightChainCombinedActual
end