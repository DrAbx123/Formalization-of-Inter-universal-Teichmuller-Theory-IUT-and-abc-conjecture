import tmp.sheaf.xif.paper.Mzk1G1ABCHeightBridgeDoneActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveProjActual
import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatToACBActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ABCHeightBridgeDoneActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveProjActual
/-- The normalized ABC point as a rational number `a/c`. -/
def abcNormalizedPoint (a c : Nat) : Rat := abcTripleToPoint a c
/-- The Fermat-style projective triple attached to an ABC data triple. -/
def abcToProjective (a b c : Nat) : Fin 3 → Rat := ![abcNormalizedPoint a c, (b : Rat) / c, 1]
theorem abcToProjective_third (a b c : Nat) : abcToProjective a b c 2 = 1 := by
  simp [abcToProjective]
theorem abcToProjective_ne_zero (a b c : Nat) : abcToProjective a b c ≠ 0 := by
  intro h
  have h2 := congrFun h 2
  simp [abcToProjective] at h2
#print axioms abcToProjective_ne_zero
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatToACBActual
end