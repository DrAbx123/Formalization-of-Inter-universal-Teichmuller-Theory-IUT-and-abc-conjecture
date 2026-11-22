import tmp.sheaf.xif.paper.Mzk1G1ABCHeightBridgeDone2Actual
import tmp.sheaf.xif.paper.Mzk1G1EllipticHeightCriterionActual
import tmp.sheaf.xif.paper.Mzk1G1RadicalSupportFinal2Actual
import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1ABCHeightBridgeFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ABCHeightBridgeDone2Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1RadicalSupportFinal2Actual
/-- Final G1 height/radical bridge for an actual ABC triple. -/
theorem abcHeightBridgeFinal {a b c : Nat} (h : IsABCTriple a b c) :
    Height.logHeight₁ (abcTripleToPoint a c) = Real.log (c : Real) ∧
      freyConductor a b c = LeanFormal.IUT.radical (a * b * c) ∧
      0 < freyConductor a b c :=
  ⟨abc_point_height_eq_log_c h, abc_freyConductor_eq_radical a b c,
    freyConductor_pos a b c⟩
#print axioms abcHeightBridgeFinal
end LeanFormal.IUT.XiFPaper.Mzk1G1ABCHeightBridgeFinalActual
end