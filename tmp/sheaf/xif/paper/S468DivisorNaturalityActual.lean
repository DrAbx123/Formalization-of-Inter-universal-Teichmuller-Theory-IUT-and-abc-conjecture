import tmp.sheaf.xif.paper.S457DivisorMapActual
import tmp.sheaf.xif.paper.S456RationalInclusionActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S412DvTriangleTauActual
open LeanFormal.IUT.XiFPaper.S457DivisorMapActual
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open Iut.SourceFinitePlaceReconstruction
open Additive

universe u

variable {K : Type u} [Field K]

/-- Explicit valuation family on the size-aligned field covers. -/
abbrev DvSmallValuationFamily : Type (u + 1) :=
  ∀ X : Example32SmallBase K,
    DvCoverNormalizedValuationData K (coverField X)

/-- Compatibility of the valuation family with function-field inclusion:
the X-valuation of the pullback equals the Y-valuation of the source. -/
def DvSmallValuationCompatibility
    (V : DvSmallValuationFamily (K := K)) : Prop :=
  ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y) (x : (coverField Y)ˣ),
    (V X).valuation (unitInclusionPullback f x) = (V Y).valuation x

/-- Conditional divisor naturality for pullback f := Units.map (arrowAlgebraMap f).
No norm is used. -/
theorem divisorMap_naturality
    (V : DvSmallValuationFamily (K := K))
    (hV : DvSmallValuationCompatibility (K := K) V)
    {X Y : Example32SmallBase K} (f : X ⟶ Y)
    (x : (coverField Y)ˣ) :
    divisorMap (K := K) (L := coverField X) (V X)
        (Additive.ofMul (unitInclusionPullback f x)) =
      divisorMap (K := K) (L := coverField Y) (V Y)
        (Additive.ofMul x) := by
  rw [divisorMap_apply, divisorMap_apply]
  exact congrArg intToStageDivisorGrothendieck (hV f x)

/-- Conditional naturality package for the explicit valuation family. -/
structure DvSmallDivisorNaturalityData where
  valuationFamily : DvSmallValuationFamily (K := K)
  compatibility : DvSmallValuationCompatibility (K := K) valuationFamily
  naturality : ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y)
    (x : (coverField Y)ˣ),
    divisorMap (K := K) (L := coverField X) (valuationFamily X)
        (Additive.ofMul (unitInclusionPullback f x)) =
      divisorMap (K := K) (L := coverField Y) (valuationFamily Y)
        (Additive.ofMul x)

end LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual

end
