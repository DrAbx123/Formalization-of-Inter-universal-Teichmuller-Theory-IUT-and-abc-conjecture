import tmp.sheaf.xif.paper.Mzk1G1ABCHeightBridgeDone2Actual
import tmp.sheaf.xif.paper.Mzk1G1EllipticHeightCriterionActual
import tmp.sheaf.xif.paper.Mzk1G1RadicalEqActual
import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1HeightBridgeFinal2Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1ABCHeightBridgeDone2Actual
/-- Final height bridge: point height is `log c` and the Frey conductor is the
standard radical. -/
theorem heightBridgeFinal2 {a b c : Nat} (h : IsABCTriple a b c) :
    Height.logHeight₁ (abcTripleToPoint a c) = Real.log (c : Real) ∧
      freyConductor a b c = LeanFormal.IUT.radical (a * b * c) :=
  ⟨abc_point_height_eq_log_c h, abc_freyConductor_eq_radical a b c⟩
#print axioms heightBridgeFinal2
end LeanFormal.IUT.XiFPaper.Mzk1G1HeightBridgeFinal2Actual
end