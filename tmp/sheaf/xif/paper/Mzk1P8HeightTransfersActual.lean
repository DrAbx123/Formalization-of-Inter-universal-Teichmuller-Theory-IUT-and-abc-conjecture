import LeanFormal.IUT.ABCBridge.Geometry.ABCModelHeightComparison
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT
namespace LeanFormal.IUT.XiFPaper.Mzk1P8HeightTransfersActual
theorem p8_frey_j_height_upper_of_point (a b c : Nat) (h : IsABCTriple a b c) (B : ℝ)
    (hpoint : Height.logHeight₁ (abcRationalPoint a c) ≤ B) :
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    Height.logHeight₁ (rationalFreyWeierstrassCurve a b).j ≤ 6 * B + Real.log 256 :=
  (rationalFreyWeierstrassCurve_height_upper_bound_transfers h B).2.2.2 hpoint
theorem p8_point_height_upper_of_frey_j (a b c : Nat) (h : IsABCTriple a b c) (B : ℝ)
    (hj : letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h;
      Height.logHeight₁ (rationalFreyWeierstrassCurve a b).j ≤ B) :
    Height.logHeight₁ (abcRationalPoint a c) ≤ (B - Real.log (27 / 64 : ℝ)) / 6 :=
  (rationalFreyWeierstrassCurve_height_upper_bound_transfers h B).2.2.1 hj
#print axioms p8_frey_j_height_upper_of_point
#print axioms p8_point_height_upper_of_frey_j
end LeanFormal.IUT.XiFPaper.Mzk1P8HeightTransfersActual
end