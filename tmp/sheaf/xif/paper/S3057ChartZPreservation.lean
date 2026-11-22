import tmp.sheaf.xif.paper.S3054ProjectiveTransport
import tmp.sheaf.xif.paper.S3055RingAutoOfChartZ
import tmp.sheaf.xif.paper.S3056GluingUniqueness
import tmp.sheaf.xif.paper.S2858AlphaOverActual
import tmp.sheaf.xif.paper.S2857GlobalAlphaCompatActual
import tmp.sheaf.xif.paper.S3059SpecMapComparison
import tmp.sheaf.xif.paper.S2801E37ProjectiveClosure
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveScheme

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3054ProjectiveTransport
open LeanFormal.IUT.XiFPaper.S3055RingAutoOfChartZ
open LeanFormal.IUT.XiFPaper.S3056GluingUniqueness
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2857GlobalAlphaCompatActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0
namespace LeanFormal.IUT.XiFPaper.S3057ChartZPreservation
local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

/-- Chart-Z preservation: the composite ChartZMap ≫ β factors through ChartZMap. -/
def S3057ChartZPreserved
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X) : Prop :=
  ∃ z : S2801E37AffineScheme S2844D6F6BaseChangeActual.K ⟶
      S2801E37AffineScheme S2844D6F6BaseChangeActual.K,
    S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ β.left =
      z ≫ S2820E37ChartZMap S2844D6F6BaseChangeActual.K

/-- The identity preserves chart-Z, actual. -/
theorem S3057_id_chartZ : S3057ChartZPreserved (𝟙 S2844X) := by
  refine ⟨𝟙 _, ?_⟩
  simp

/-- The global alpha preserves chart-Z, actual from S3059. -/
theorem S3057_alpha_chartZ : S3057ChartZPreserved alphaOverS2844 := by
  refine ⟨S2853ChartZSchemeEndo S2844D6F6BaseChangeActual.K, ?_⟩
  exact S3059SpecMapComparison S2844D6F6BaseChangeActual.K

/-- Exact target: every order-two origin-preserving scheme auto preserves the
chart-Z open. -/
def S3057ChartZPreservationTarget : Prop :=
  ∀ β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X,
    β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X →
    S2888OriginPreserving β → S3057ChartZPreserved β

/-!
## Exact target and first error

S3057ChartZPreservationTarget: every order-2 origin-preserving β preserves the
chart-Z affine open.

Actual: the identity and global alpha branches both preserve chart-Z
(S3057_id_chartZ; S3057_alpha_chartZ from S3059).

First error: no proof for an arbitrary β.  The missing step is to use the
universal property of the chart-Z affine open S2801E37AffineScheme (or the
ChartZMap open immersion) to show that ChartZMap ≫ β factors through ChartZMap
for order-2 origin-preserving β.  Nothing here is faked.
-/

#check S3057ChartZPreserved
#check S3057_id_chartZ
#check S3057_alpha_chartZ
#check S3057ChartZPreservationTarget
#print axioms S3057_alpha_chartZ

end LeanFormal.IUT.XiFPaper.S3057ChartZPreservation
end
