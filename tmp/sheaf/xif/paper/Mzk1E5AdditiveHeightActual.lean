import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison
import tmp.sheaf.xif.paper.S3131PaperRouteHeightReductionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1E5AdditiveHeightActual — E-5 (b): additive height bound + volume dominance

DAG nodes: e-deep:E5.uniformHeightConsumer / iutiv-abc:HW.add.  Connects the
version-2 additive height-weight bound to the undilated height interface: at
epsilon = 1 the additive bound gives height <= 2*weight + A; if the comparison
region log-volume dominates 2*weight + A, the undilated height bound (b) follows.
The volume-dominance hypothesis is explicit (the IUT IV section-2 inequality).
No closure claim; gate NOT PASSED.  Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1E5AdditiveHeightActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteFieldStatementsActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteHeightReductionActual

universe u

/-- Additive bound (at eps=1) plus region-volume dominance gives (b). -/
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

/-- The concrete constant A supplied by the additive bound. -/
theorem exists_additive_constant (h : ABCHeightWeightAdditiveBoundV2) :
    ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        2 * arithmeticWeight (abcRationalPoint a c) + A :=
  simpa [show (1 : Real) + 1 = 2 by norm_num] using
    ABCHeightWeightAdditiveBoundV2.exists_constant h (by norm_num : (0 : Real) < 1)

/-- Combined consumer: additive bound + explicit volume dominance -> (b) family. -/
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

/-- Rows: cross-node status. -/
def e5AdditiveRows : List (String × String × String) :=
  [ ("additive + volume -> undilated height", "undilatedHeightBound_of_additiveBound_volume", "PROVED (conditional on explicit volume dominance)"),
    ("constant extraction", "exists_additive_constant", "PROVED"),
    ("(b) family consumer", "heightComparisonFamily_of_additiveBound_volume", "PROVED (conditional)"),
    ("named inputs", "ABCHeightWeightAdditiveBoundV2 + region-volume dominance", "NAMED/EXPLICIT"),
    ("scope", "no closure; gate NOT PASSED", "INTEGRITY") ]

theorem e5AdditiveRows_length : e5AdditiveRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1E5AdditiveHeightActual

end
