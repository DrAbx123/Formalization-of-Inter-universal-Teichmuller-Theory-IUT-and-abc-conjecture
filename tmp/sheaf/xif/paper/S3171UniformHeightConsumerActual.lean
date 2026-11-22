import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison
import tmp.sheaf.xif.paper.S3131PaperRouteHeightReductionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3171c: (b) uniform height comparison from the pinned Mathlib height layer

Consumes the production H1 conditional reduction
LeanFormal/IUT/ABCBridge/Arithmetic/ABCHeightArithmeticWeightComparison.lean
(which imports the pinned Mathlib.NumberTheory.Height.NumberField):
* abcRationalPoint_logHeight₁_eq_sum_arithmeticPrimeSupport
* abcRationalPoint_logHeight₁_le_mul_arithmeticWeight_of_uniform_valuation_bound
* abcRationalPoint_logHeight₁_le_oneAdd_mul_arithmeticWeight_of_valuation_bound.

It connects the uniform valuation bound of the actual ABC point to the (b)
UNDILATED height interface of the paper route
(S3131PaperRouteHeightReductionActual.UndilatedHeightBound): if the route's
log-volume of the comparison-region point dominates B * arithmeticWeight of the
point, then the uniform height comparison gives the undilated height bound.

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3171UniformHeightConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteFieldStatementsActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteHeightReductionActual

universe u

/-- The uniform Mathlib-height comparison at a fixed triple (reused production
theorem; the only input is the uniform valuation bound). -/
theorem uniformHeightComparison_of_valuation_bound
    {a b c : ℕ} (h : IsABCTriple a b c) {B : ℝ}
    (hbound : ∀ p ∈ arithmeticPrimeSupport (abcRationalPoint a c),
      max 0 (-(padicValRat p (abcRationalPoint a c) : ℝ)) ≤ B) :
    Height.logHeight₁ (abcRationalPoint a c) ≤
      B * arithmeticWeight (abcRationalPoint a c) :=
  abcRationalPoint_logHeight₁_le_mul_arithmeticWeight_of_uniform_valuation_bound h hbound

/-- **(b) undilated height bound from the uniform valuation bound**, given that
the route's comparison-region log-volume dominates B * arithmeticWeight. -/
theorem undilatedHeightBound_of_valuation_bound
    {X : Type u} {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    {B : ℝ}
    (hbound : ∀ a b c : Nat, IsABCTriple a b c →
      ∀ p ∈ arithmeticPrimeSupport (abcRationalPoint a c),
        max 0 (-(padicValRat p (abcRationalPoint a c) : ℝ)) ≤ B)
    (hvol : ∀ a b c : Nat, IsABCTriple a b c →
      B * arithmeticWeight (abcRationalPoint a c) ≤
        (W.logVolume {pt a b c}).toReal) :
    UndilatedHeightBound W pt := by
  intro a b c habc
  have h1 := uniformHeightComparison_of_valuation_bound habc (hbound a b c habc)
  have h2 := hvol a b c habc
  linarith

/-- The (b) family through the uniform height comparison (heightComparisonFamily
of the undilated bound). -/
theorem heightComparisonFamily_of_valuation_bound
    {X : Type u} {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    {B : ℝ}
    (hbound : ∀ a b c : Nat, IsABCTriple a b c →
      ∀ p ∈ arithmeticPrimeSupport (abcRationalPoint a c),
        max 0 (-(padicValRat p (abcRationalPoint a c) : ℝ)) ≤ B)
    (hvol : ∀ a b c : Nat, IsABCTriple a b c →
      B * arithmeticWeight (abcRationalPoint a c) ≤
        (W.logVolume {pt a b c}).toReal) :
    HeightComparisonFamily W pt :=
  heightComparisonFamily_of_undilated (undilatedHeightBound_of_valuation_bound hbound hvol)

/-- The pinned-asset witness record: (production decl, role). -/
def s3171HeightAssetWitnesses : List (String × String) :=
  [ ("Mathlib.NumberTheory.Height.NumberField", "pinned canonical height Height.logHeight₁"),
    ("abcRationalPoint_logHeight₁_eq_sum_arithmeticPrimeSupport", "dictionary expansion of the ABC-point height"),
    ("abcRationalPoint_logHeight₁_le_mul_arithmeticWeight_of_uniform_valuation_bound", "H1 uniform valuation bound => height <= B*weight"),
    ("abcRationalPoint_logHeight₁_le_oneAdd_mul_arithmeticWeight_of_valuation_bound", "(1+eps)-normalized H1 shape"),
    ("S3171IUTIVSection1DisplayActual.abcConjecture_of_undilated", "assembly of (b)/(c) to ABC") ]

end LeanFormal.IUT.XiFPaper.S3171UniformHeightConsumerActual

end
