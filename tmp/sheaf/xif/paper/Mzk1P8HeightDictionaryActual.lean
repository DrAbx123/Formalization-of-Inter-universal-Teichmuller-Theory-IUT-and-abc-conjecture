import LeanFormal.IUT.ABCBridge.Geometry.ABCModelHeightComparison
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary
import tmp.sheaf.xif.paper.Mzk1P6PaperBoundActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P6PaperBoundActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P8HeightDictionaryActual
theorem p8_perTriple_dictionary
    {a b c : Nat} (h : IsABCTriple a b c) (B : ℝ)
    (hpoint : Height.logHeight₁ (abcRationalPoint a c) ≤ B) :
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    Height.logHeight₁ (rationalFreyWeierstrassCurve a b).j ≤ 6 * B + Real.log 256 ∧
      (c : ℝ) ≤ Real.exp B := by
  letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
  have htrans := rationalFreyWeierstrassCurve_height_upper_bound_transfers h B
  refine ⟨htrans.2.2.2 hpoint, ?_⟩
  have hlog : Real.log (c : ℝ) ≤ B := by
    rwa [← abcRationalPoint_logHeight₁ h]
  have hc : 0 < c := h.c_pos
  have hcpos : (0 : ℝ) < (c : ℝ) := by
    exact_mod_cast hc
  exact (Real.log_le_iff_le_exp hcpos).mp hlog
theorem p8_perTriple_from_p6PaperBound
    {a b c : Nat} (h : IsABCTriple a b c) (n : Nat) (D Q S T : ℝ)
    (hpoint : Height.logHeight₁ (abcRationalPoint a c) ≤ p6PaperBound n D Q S T) :
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    Height.logHeight₁ (rationalFreyWeierstrassCurve a b).j ≤
      6 * p6PaperBound n D Q S T + Real.log 256 ∧
      (c : ℝ) ≤ Real.exp (p6PaperBound n D Q S T) :=
  p8_perTriple_dictionary h (p6PaperBound n D Q S T) hpoint
#print axioms p8_perTriple_from_p6PaperBound
end LeanFormal.IUT.XiFPaper.Mzk1P8HeightDictionaryActual
end