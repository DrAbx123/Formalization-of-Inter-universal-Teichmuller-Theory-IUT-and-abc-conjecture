import LeanFormal.IUT.ABCBridge.Geometry.ABCModelHeightComparison
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary
import tmp.sheaf.xif.paper.Mzk1P6PaperBoundActual
import Mathlib.Tactic

set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P6PaperBoundActual

namespace LeanFormal.IUT.XiFPaper.Mzk1P8HeightFromIVActual

/-- Per-triple dictionary: a bound on the abc point height gives the Frey
j-height bound and the elementary `c` bound. -/
theorem p8_perTriple_heightDictionary
    {a b c : Nat} (h : IsABCTriple a b c) (B : Real)
    (hpoint : Height.logHeight₁ (abcRationalPoint a c) ≤ B) :
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    Height.logHeight₁ (rationalFreyWeierstrassCurve a b).j ≤
        6 * B + Real.log 256 ∧
      (c : Real) ≤ Real.exp B := by
  letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
  have htrans := rationalFreyWeierstrassCurve_height_upper_bound_transfers h B
  refine ⟨htrans.2.2.2 hpoint, ?_⟩
  have hcpos : (0 : Real) < (c : Real) := by
    exact_mod_cast h.1.trans_le (Nat.le_add_right a b)
  have hlog : Real.log (c : Real) ≤ B := by
    rwa [← abcRationalPoint_logHeight₁ h]
  exact (Real.log_le_iff_le_exp hcpos).mp hlog

/-- Per-triple dictionary in the reverse direction: a Frey j-height bound
gives the abc point-height bound with the exact constant. -/
theorem p8_perTriple_pointHeight_of_freyJHeight
    {a b c : Nat} (h : IsABCTriple a b c) (B : Real)
    (hj : letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h;
      Height.logHeight₁ (rationalFreyWeierstrassCurve a b).j ≤ B) :
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (B - Real.log (27 / 64 : Real)) / 6 := by
  letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
  exact (rationalFreyWeierstrassCurve_height_upper_bound_transfers h B).2.2.1 hj

/-- Per-triple P6-IV input: if the abc point height is bounded by the P6 paper
bound `(l+5)/4 D - (l+1)/24 Q + S + (l+5)T`, then both the Frey j-height and
`c` are bounded by the corresponding actual expressions. -/
theorem p8_perTriple_heightBound_from_p6PaperBound
    {a b c : Nat} (h : IsABCTriple a b c)
    (n : Nat) (D Q S T : Real)
    (hpoint : Height.logHeight₁ (abcRationalPoint a c) ≤
      p6PaperBound n D Q S T) :
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    Height.logHeight₁ (rationalFreyWeierstrassCurve a b).j ≤
        6 * p6PaperBound n D Q S T + Real.log 256 ∧
      (c : Real) ≤ Real.exp (p6PaperBound n D Q S T) :=
  p8_perTriple_heightDictionary h (p6PaperBound n D Q S T) hpoint

#print axioms p8_perTriple_heightDictionary
#print axioms p8_perTriple_pointHeight_of_freyJHeight
#print axioms p8_perTriple_heightBound_from_p6PaperBound

end LeanFormal.IUT.XiFPaper.Mzk1P8HeightFromIVActual
end