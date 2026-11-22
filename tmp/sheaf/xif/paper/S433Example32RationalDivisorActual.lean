import tmp.sheaf.xif.paper.S412DvTriangleTauActual
import tmp.sheaf.xif.paper.DvTriangleFieldCoversActual

/-!
# S433: Example 3.2 rational functions and divisor data

For a finite étale field cover L/K, rationalFunctions = L^× and the divisor
coefficient is the normalized valuation from S412, i.e. the integer N in
N * log(q_v).  The construction is conditional on the actual q_v normalized
valuation extension on L; the missing global valuation family and pullback
naturality are recorded exactly, not faked.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

namespace LeanFormal.IUT.XiFPaper.S433Example32RationalDivisorActual

open CategoryTheory
open LeanFormal.IUT.XiFPaper.DvTriangleFieldCoversActual
open LeanFormal.IUT.XiFPaper.S412DvTriangleTauActual

universe u

variable {K : Type u} [Field K]

section Cover

variable (L : DvTriangleFieldCover K)
variable [Field L.obj.obj] [Algebra K L.obj.obj]
variable (V : DvCoverNormalizedValuationData K L.obj.obj)

/-- Example 3.2 rational functions on the field cover: L^×. -/
abbrev example32RationalFunctions : Type u := L.obj.objˣ

/-- Divisor coefficient N in N * log(q_v): the normalized valuation of a
rational function. -/
def example32DivisorCoefficient (x : example32RationalFunctions L) : ℤ :=
  Multiplicative.toAdd (V.valuation x)

/-- The divisor coefficient is additive on rational functions. -/
theorem example32DivisorCoefficient_mul
    (x y : example32RationalFunctions L) :
    example32DivisorCoefficient L V (x * y) =
      example32DivisorCoefficient L V x + example32DivisorCoefficient L V y := by
  simp [example32DivisorCoefficient, map_mul]

/-- The divisor coefficient of the unit rational function is zero. -/
theorem example32DivisorCoefficient_one :
    example32DivisorCoefficient L V (1 : example32RationalFunctions L) = 0 := by
  simp [example32DivisorCoefficient]

/-- Conditional per-cover Example 3.2 rational-function/divisor data. -/
structure Example32CoverRationalDivisorData where
  divisorCoefficient : example32RationalFunctions L → ℤ
  divisorCoefficient_eq : divisorCoefficient =
    example32DivisorCoefficient L V
  divisor_additive : ∀ x y, divisorCoefficient (x * y) =
    divisorCoefficient x + divisorCoefficient y
  qValuation : ℤ
  qValuation_eq : qValuation = V.qValuation

/-- Conditional constructor from the S412 normalized valuation data. -/
noncomputable def example32CoverRationalDivisorData :
    Example32CoverRationalDivisorData L V where
  divisorCoefficient := example32DivisorCoefficient L V
  divisorCoefficient_eq := rfl
  divisor_additive := example32DivisorCoefficient_mul L V
  qValuation := V.qValuation
  qValuation_eq := rfl

end Cover

/-- Exact missing datum: a q_v normalized valuation extension on every finite
étale field cover, uniformly over S398's D_v^⊢. -/
def Example32QValuationFamilyRequired : Prop :=
  ∀ (L : DvTriangleFieldCover K) [Field L.obj.obj] [Algebra K L.obj.obj],
    Nonempty (DvCoverNormalizedValuationData K L.obj.obj)

/-- Exact missing pullback/naturality datum for the divisor coefficients.  The
repo has no canonical pullback L'^× → L^× along an algebra-cover morphism. -/
structure Example32DivisorPullbackData where
  pullback : ∀ {L L' : DvTriangleFieldCover K}
    [Field L.obj.obj] [Algebra K L.obj.obj]
    [Field L'.obj.obj] [Algebra K L'.obj.obj]
    (V : DvCoverNormalizedValuationData K L.obj.obj)
    (V' : DvCoverNormalizedValuationData K L'.obj.obj)
    (f : L ⟶ L'), L'.obj.objˣ → L.obj.objˣ
  divisor_naturality : Prop

/-- Exact missing full Example 3.2 divisor naturality/pullback object. -/
def Example32DivisorNaturalityRequired : Prop :=
  Nonempty (Example32DivisorPullbackData (K := K))

end LeanFormal.IUT.XiFPaper.S433Example32RationalDivisorActual

end
