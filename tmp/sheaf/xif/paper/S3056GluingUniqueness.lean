import tmp.sheaf.xif.paper.S3055RingAutoOfChartZ
import tmp.sheaf.xif.paper.S2858AlphaOverActual
import tmp.sheaf.xif.paper.S2888OriginPreservingOrderTwo
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3054ProjectiveTransport
open LeanFormal.IUT.XiFPaper.S3055RingAutoOfChartZ
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S3030AffineOriginClassification
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2888OriginPreservingOrderTwo
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0
namespace LeanFormal.IUT.XiFPaper.S3056GluingUniqueness

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual.K :=
  S2847A6.fieldF
local instance : NumberField LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual.K :=
  S2847A6.numberFieldF
local instance : DecidableEq LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual.K :=
  Classical.decEq _

/-- Exact gluing uniqueness: two scheme endomorphisms with equal chart-Z and
chart-Y components are equal. -/
def S3056GluingUniqueness : Prop :=
  ∀ β γ : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X,
    S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ β.left =
      S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ γ.left →
    S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫ (show S2820E37ProjectiveScheme S2844D6F6BaseChangeActual.K ⟶ S2820E37ProjectiveScheme S2844D6F6BaseChangeActual.K from β.left) =
      S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫ (show S2820E37ProjectiveScheme S2844D6F6BaseChangeActual.K ⟶ S2820E37ProjectiveScheme S2844D6F6BaseChangeActual.K from γ.left) →
    β = γ

/-- Actual application: equal chart-Z and chart-Y components force equality. -/
theorem S3056_eq_of_components
    (h : S3056GluingUniqueness)
    (β γ : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (hZ : S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ β.left =
      S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ γ.left)
    (hY : S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫ (show S2820E37ProjectiveScheme S2844D6F6BaseChangeActual.K ⟶ S2820E37ProjectiveScheme S2844D6F6BaseChangeActual.K from β.left) =
      S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫ (show S2820E37ProjectiveScheme S2844D6F6BaseChangeActual.K ⟶ S2820E37ProjectiveScheme S2844D6F6BaseChangeActual.K from γ.left)) :
    β = γ :=
  h β γ hZ hY

/-- Conditional projective classification using S3055 restriction and S3056
gluing plus the S3054 branch comparison. -/
theorem S3056_classification_of_data
    (hglue : S3054GluingData)
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (hβ : β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X)
    (horg : S2888OriginPreserving β)
    (D : S3055RingAutoOfChartZ β) :
    β = 𝟙 S2844D6F6BaseChangeActual.S2844X ∨ β = alphaOverS2844 :=
  S3054_classification_of_restriction_and_gluing hglue β hβ horg
    (S3055_toChartZRestriction β D)

/-!
## Exact statement and first error

S3056GluingUniqueness is the exact chart-Z/chart-Y gluing uniqueness for
arbitrary scheme endomorphisms of the glued projective S2844X.

Actual: S3056_eq_of_components is its unpacking; S3056_classification_of_data
combines S3055 restriction and S3054/S3053 affine classification.

First error: S3056GluingUniqueness is not proved.  The existing glue data and
chart maps provide the two charts, but no theorem says a map out of the glued
scheme is determined by its two chart components for arbitrary endomorphisms.
No gluing uniqueness is faked.
-/

#check S3056GluingUniqueness
#check S3056_eq_of_components
#check S3056_classification_of_data
#print axioms S3056_eq_of_components
#print axioms S3056_classification_of_data

end LeanFormal.IUT.XiFPaper.S3056GluingUniqueness
end
