import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary
import LeanFormal.IUT.ABCBridge.Geometry.ABCModelHeightComparison
import tmp.sheaf.xif.paper.Mzk1G1EllipticHeightCriterionActual
import tmp.sheaf.xif.paper.Mzk1G1RadicalEqActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1ABCHeightBridgeDone2Actual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
def abcTripleToPoint (a c : Nat) : Rat := abcRationalPoint a c
def normalizedAbcRatio (a c : Nat) : Rat := (a : Rat) / (c : Rat)
theorem abcTripleToPoint_eq_normalizedAbcRatio (a c : Nat) :
    abcTripleToPoint a c = normalizedAbcRatio a c := rfl
theorem abc_point_height_eq_log_c {a b c : Nat} (h : IsABCTriple a b c) :
    Height.logHeight₁ (abcTripleToPoint a c) = Real.log (c : Real) :=
  abcRationalPoint_logHeight₁ h
theorem abc_frey_j_height_bounds {a b c : Nat} (h : IsABCTriple a b c) :
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    ((27 / 64 : Real) * (c : Real) ^ 6 <=
        Height.mulHeight₁ (rationalFreyWeierstrassCurve a b).j ∧
      Height.mulHeight₁ (rationalFreyWeierstrassCurve a b).j <= 256 * (c : Real) ^ 6) ∧
    (6 * Height.logHeight₁ (abcTripleToPoint a c) + Real.log (27 / 64 : Real) <=
        Height.logHeight₁ (rationalFreyWeierstrassCurve a b).j ∧
      Height.logHeight₁ (rationalFreyWeierstrassCurve a b).j <=
        6 * Height.logHeight₁ (abcTripleToPoint a c) + Real.log 256) :=
  rationalFreyWeierstrassCurve_j_height_bounds h
theorem abc_freyConductor_eq_radical (a b c : Nat) :
    freyConductor a b c = LeanFormal.IUT.radical (a * b * c) := by
  rw [freyConductor_eq_radical]
  exact Mzk1G1RadicalEqActual.local_radical_eq_std (a * b * c)
structure ABCHeightRadicalBridge (a b c : Nat) : Prop where
  frey_model : rationalFreyWeierstrassCurve a b = rationalFreyWeierstrassCurve a b
  point_eq : abcTripleToPoint a c = abcRationalPoint a c
  point_height_eq : Height.logHeight₁ (abcTripleToPoint a c) = Real.log (c : Real)
  conductor_eq_radical :
    freyConductor a b c = LeanFormal.IUT.radical (a * b * c)
theorem abcHeightRadicalBridge_of_isABCTriple {a b c : Nat}
    (h : IsABCTriple a b c) : ABCHeightRadicalBridge a b c where
  frey_model := rfl
  point_eq := rfl
  point_height_eq := abc_point_height_eq_log_c h
  conductor_eq_radical := abc_freyConductor_eq_radical a b c
#print axioms abc_point_height_eq_log_c
#print axioms abc_frey_j_height_bounds
#print axioms abcHeightRadicalBridge_of_isABCTriple
end LeanFormal.IUT.XiFPaper.Mzk1G1ABCHeightBridgeDone2Actual
end