import tmp.sheaf.xif.paper.S3171UniformHeightConsumerActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# Mzk1E5UniformHeightActual — E-5 (b): unit valuation bound consumer

DAG node: e-deep:E5.uniformHeightConsumer (CONDITIONAL, 1 unproved dep).
Specializes the uniform height consumer to B = 1: if every local valuation magnitude is
at most 1 and the comparison-region log-volume dominates the arithmetic weight, then the
undilated height bound holds.  This is a real consumer chain (Mathlib height layer ->
uniform bound -> undilated height -> (b) family), not a proof of the named valuation or
volume inputs.  No closure claim; gate NOT PASSED.
Registry frozen 14041; no registry edits.  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1E5UniformHeightActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteFieldStatementsActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteHeightReductionActual
open LeanFormal.IUT.XiFPaper.S3171UniformHeightConsumerActual

universe u

/-- Unit uniform valuation bound gives the undilated height bound when the comparison
region dominates the arithmetic weight. -/
theorem undilatedHeightBound_of_unit_valuation_bound
    {X : Type u} {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (hbound : ∀ a b c : Nat, IsABCTriple a b c →
      ∀ p ∈ arithmeticPrimeSupport (abcRationalPoint a c),
        max 0 (-(padicValRat p (abcRationalPoint a c) : ℝ)) ≤ 1)
    (hvol : ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        (W.logVolume {pt a b c}).toReal) :
    UndilatedHeightBound W pt := by
  intro a b c habc
  have h1 := uniformHeightComparison_of_valuation_bound habc (hbound a b c habc)
  have h2 := hvol a b c habc
  linarith

/-- The (b) height-comparison family from the unit valuation bound. -/
theorem heightComparisonFamily_of_unit_valuation_bound
    {X : Type u} {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (hbound : ∀ a b c : Nat, IsABCTriple a b c →
      ∀ p ∈ arithmeticPrimeSupport (abcRationalPoint a c),
        max 0 (-(padicValRat p (abcRationalPoint a c) : ℝ)) ≤ 1)
    (hvol : ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        (W.logVolume {pt a b c}).toReal) :
    HeightComparisonFamily W pt :=
  heightComparisonFamily_of_undilated
    (undilatedHeightBound_of_unit_valuation_bound hbound hvol)

/-- Rows for the E-5 unit-B consumer. -/
def e5UnitConsumerRows : List (String × String × String) :=
  [ ("Mathlib uniform height comparison", "uniformHeightComparison_of_valuation_bound (B=1 specialization)", "PROVED (reuse)"),
    ("undilated height bound", "undilatedHeightBound_of_unit_valuation_bound", "PROVED (conditional on named valuation/volume inputs)"),
    ("(b) family", "heightComparisonFamily_of_unit_valuation_bound", "PROVED (conditional)"),
    ("named inputs", "unit valuation bound; comparison-region volume dominance", "NAMED (not proved)"),
    ("scope", "real consumer chain only; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem e5UnitConsumerRows_length : e5UnitConsumerRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1E5UniformHeightActual

end
