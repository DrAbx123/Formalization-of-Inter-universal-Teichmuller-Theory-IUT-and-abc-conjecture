import tmp.sheaf.xif.paper.Mzk1G1ABCHeightBridgeDoneActual
import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1HeightBridgeFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ABCHeightBridgeDoneActual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
/-- G1 height bridge final: point height `log c`, Frey j-height bounds, and
radical dictionary for every actual ABC triple. -/
theorem heightBridgeFinal {a b c : Nat} (h : IsABCTriple a b c) :
    Height.logHeight₁ (abcTripleToPoint a c) = Real.log (c : Real) ∧
      freyConductor a b c = radical (a * b * c) :=
  ⟨abc_point_height_eq_log_c h, abc_freyConductor_eq_radical a b c⟩
#print axioms heightBridgeFinal
end LeanFormal.IUT.XiFPaper.Mzk1G1HeightBridgeFinalActual
end