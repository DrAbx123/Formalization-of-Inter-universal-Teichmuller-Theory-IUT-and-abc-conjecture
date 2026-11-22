import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison
import tmp.sheaf.xif.paper.S3131PaperRouteHeightReductionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1E5AdditiveHeightActualV2 — E-5 (b): additive bound + volume dominance

DAG nodes: e-deep:E5.uniformHeightConsumer / iutiv-abc:HW.add.  At eps=1 the
additive contract gives height <= 2*weight + A; if the comparison-region log-volume
dominates 2*weight + A, the undilated height bound (b) follows.  Explicit volume
dominance; no closure; gate NOT PASSED.  Registry 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1E5AdditiveHeightActualV2

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteFieldStatementsActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteHeightReductionActual

universe u

theorem undilatedHeightBound_of_additiveBound_volume {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (h : ABCHeightWeightAdditiveBoundV2) {A : Real}
    (hA : ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        2 * arithmeticWeight (abcRationalPoint a c) + A)
    (hvol : ∀ a b c : Nat, IsABCTriple a b c →
      2 * arithmeticWeight (abcRationalPoint a c) + A ≤
        (W.logVolume {pt a b c}).toReal) :
    UndilatedHeightBound W pt := by
  intro a b c habc
  have h1 := hA a b c habc
  have h2 := hvol a b c habc
  linarith

theorem exists_additive_constant (h : ABCHeightWeightAdditiveBoundV2) :
    ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        2 * arithmeticWeight (abcRationalPoint a c) + A := by
  simpa [show (1 : Real) + 1 = 2 by norm_num] using
    ABCHeightWeightAdditiveBoundV2.exists_constant h (by norm_num : (0 : Real) < 1)

theorem heightComparisonFamily_of_additiveBound_volume {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (h : ABCHeightWeightAdditiveBoundV2) {A : Real}
    (hA : ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        2 * arithmeticWeight (abcRationalPoint a c) + A)
    (hvol : ∀ a b c : Nat, IsABCTriple a b c →
      2 * arithmeticWeight (abcRationalPoint a c) + A ≤
        (W.logVolume {pt a b c}).toReal) :
    HeightComparisonFamily W pt :=
  heightComparisonFamily_of_undilated
    (undilatedHeightBound_of_additiveBound_volume h hA hvol)

def e5AdditiveRowsV2 : List (String × String × String) :=
  [ ("additive + volume -> undilated height", "undilatedHeightBound_of_additiveBound_volume", "PROVED (conditional)"),
    ("constant extraction", "exists_additive_constant", "PROVED"),
    ("(b) family", "heightComparisonFamily_of_additiveBound_volume", "PROVED (conditional)"),
    ("scope", "explicit volume dominance; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem e5AdditiveRowsV2_length : e5AdditiveRowsV2.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1E5AdditiveHeightActualV2

end
