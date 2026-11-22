import tmp.sheaf.xif.paper.S2913ChartFactorizationAttempt
import tmp.sheaf.xif.paper.S3058ChartZPreservation
import tmp.sheaf.xif.paper.S3057GluingUniquenessActual
import tmp.sheaf.xif.paper.S2876NontrivialAlphaActual
import tmp.sheaf.xif.paper.S3055RingAutoOfChartZ

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2913ChartFactorizationAttempt
open LeanFormal.IUT.XiFPaper.S3058ChartZPreservation
open LeanFormal.IUT.XiFPaper.S3055RingAutoOfChartZ
open LeanFormal.IUT.XiFPaper.S3057GluingUniquenessActual
open LeanFormal.IUT.XiFPaper.S2876NontrivialAlphaActual
open LeanFormal.IUT.XiFPaper.S2888OriginPreservingOrderTwo
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3060ChartZFromOriginToChart

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

/-- Exact builder needed from S2913: every chart factorization gives the
chart-Z ring-auto data. -/
def S3060FactorizationBuilder : Prop :=
  ∀ (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X),
    S2913ChartFactorization β → Nonempty (S3055RingAutoOfChartZ β)

/-- Conditional S3058 target from S2913OriginToChart plus the factorization
builder. -/
theorem S3060_of_originToChart
    (h : S2913OriginToChart) (hbuilder : S3060FactorizationBuilder) :
    S3058ChartZPreservationTarget := by
  intro β hβ horig
  rcases h β hβ horig with ⟨F⟩
  exact hbuilder β F

/-- S2913OriginToChart is FALSE as stated: the identity β = 1 is order-two and
origin-preserving, but hoverlap forces the chart-Z factor to be alpha. -/
theorem S3060_originToChart_false : ¬ S2913OriginToChart := by
  intro h
  rcases h (𝟙 S2844D6F6BaseChangeActual.S2844X) (by simp)
    S2888_id_originPreserving with ⟨F⟩
  have hZ : S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫
      (Over.Hom.left (𝟙 S2844D6F6BaseChangeActual.S2844X)) =
      S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫
        Over.Hom.left alphaOverS2844 := by
    rw [F.hZ, F.hoverlap, F.hZalpha]
  have hY : S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫
      (Over.Hom.left (𝟙 S2844D6F6BaseChangeActual.S2844X)) =
      S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫
        Over.Hom.left alphaOverS2844 :=
    F.hY
  have heq : (𝟙 S2844D6F6BaseChangeActual.S2844X) = alphaOverS2844 :=
    S3057_gluingUniqueness _ _ hZ hY
  exact S2876_alphaOverS2844_ne_id heq.symm

/-!
## Exact construction and first error

Actual:
* S3060FactorizationBuilder: exact missing builder from S2913 chart
  factorization to S3055RingAutoOfChartZ.
* S3060_of_originToChart: combines S2913OriginToChart and the builder to give
  S3058ChartZPreservationTarget.
* S3060_originToChart_false: S2913OriginToChart is FALSE as stated.

The falsehood is the key first error: S2913ChartFactorization contains
hoverlap : z = S2853ChartZSchemeEndo.  Applying S2913OriginToChart to the
identity (order-two, origin-preserving) forces the chart-Z factor to be the
alpha endomorphism.  Comparing chart-Z and chart-Y components with alpha and
applying the actual S3057_gluingUniqueness gives 1 = alphaOverS2844, which
contradicts S2876_alphaOverS2844_ne_id.

Correct input: a branch-dependent origin-to-chart factorization with
z = id (identity branch) or z = S2853ChartZSchemeEndo (alpha branch).
The current S2913 input covers only the alpha branch, so S3060 cannot use it for
the identity branch; no factorization is faked.
-/

#print axioms S3060_of_originToChart
#print axioms S3060_originToChart_false

end LeanFormal.IUT.XiFPaper.S3060ChartZFromOriginToChart
end
