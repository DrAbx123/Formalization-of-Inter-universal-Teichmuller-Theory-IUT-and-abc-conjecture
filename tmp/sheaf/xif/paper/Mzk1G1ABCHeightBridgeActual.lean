import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary
import LeanFormal.IUT.ABCBridge.Geometry.ABCModelHeightComparison
import tmp.sheaf.xif.paper.Mzk1G1EllipticHeightCriterionActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1ABCHeightBridgeActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open Polynomial
/-- The rational Frey curve attached to an ABC pair `(a,b)`. -/
abbrev abcTripleToFrey (a b : ℕ) : WeierstrassCurve ℚ :=
  rationalFreyWeierstrassCurve a b
/-- The normalized ABC rational point `a/c`. -/
def abcTripleToPoint (a c : ℕ) : ℚ :=
  abcRationalPoint a c
/-- The normalized ratio `a/c` as a rational number. -/
def normalizedAbcRatio (a c : ℕ) : ℚ := (a : ℚ) / (c : ℚ)
theorem abcTripleToPoint_eq_normalizedAbcRatio (a c : ℕ) :
    abcTripleToPoint a c = normalizedAbcRatio a c := rfl
/-- Height dictionary: the canonical point height is `log c`. -/
theorem abc_point_height_eq_log_c {a b c : ℕ} (h : IsABCTriple a b c) :
    Height.logHeight₁ (abcTripleToPoint a c) = Real.log (c : ℝ) :=
  abcRationalPoint_logHeight₁ h
/-- Frey `j`-height bounds for the actual rational Frey model. -/
theorem abc_frey_j_height_bounds {a b c : ℕ} (h : IsABCTriple a b c) :
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    ((27 / 64 : ℝ) * (c : ℝ) ^ 6 ≤ Height.mulHeight₁ (abcTripleToFrey a b).j ∧
      Height.mulHeight₁ (abcTripleToFrey a b).j ≤ 256 * (c : ℝ) ^ 6) ∧
    (6 * Height.logHeight₁ (abcTripleToPoint a c) + Real.log (27 / 64 : ℝ) ≤
        Height.logHeight₁ (abcTripleToFrey a b).j ∧
      Height.logHeight₁ (abcTripleToFrey a b).j ≤
        6 * Height.logHeight₁ (abcTripleToPoint a c) + Real.log 256) :=
  rationalFreyWeierstrassCurve_j_height_bounds h
/-- Radical dictionary: the actual Frey conductor is the radical of `abc`. -/
theorem abc_freyConductor_eq_radical (a b c : ℕ) :
    freyConductor a b c = radical (a * b * c) :=
  freyConductor_eq_radical a b c
/-- Height/radical bridge dictionary for an actual ABC triple: the Frey model,
the normalized point, its height, the j-height bounds, and the conductor
radical identity. -/
structure ABCHeightRadicalBridge (a b c : ℕ) : Prop where
  frey_model : abcTripleToFrey a b = rationalFreyWeierstrassCurve a b
  point_eq : abcTripleToPoint a c = abcRationalPoint a c
  point_height_eq :
    Height.logHeight₁ (abcTripleToPoint a c) = Real.log (c : ℝ)
  conductor_eq_radical : freyConductor a b c = radical (a * b * c)
/-- Actual dictionary inhabitant for every ABC triple. -/
theorem abcHeightRadicalBridge_of_isABCTriple {a b c : ℕ}
    (h : IsABCTriple a b c) : ABCHeightRadicalBridge a b c where
  frey_model := rfl
  point_eq := rfl
  point_height_eq := abc_point_height_eq_log_c h
  conductor_eq_radical := abc_freyConductor_eq_radical a b c
#print axioms abc_point_height_eq_log_c
#print axioms abc_frey_j_height_bounds
#print axioms abcHeightRadicalBridge_of_isABCTriple
end LeanFormal.IUT.XiFPaper.Mzk1G1ABCHeightBridgeActual
end