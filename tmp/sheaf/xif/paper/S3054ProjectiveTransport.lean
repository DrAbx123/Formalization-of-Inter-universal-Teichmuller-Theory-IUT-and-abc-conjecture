import tmp.sheaf.xif.paper.S3053UnconditionalAffineClassification
import tmp.sheaf.xif.paper.S2820E37TransitionActual
import tmp.sheaf.xif.paper.S2858AlphaOverActual
import tmp.sheaf.xif.paper.S2801E37ProjectiveClosure

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3053UnconditionalAffineClassification
open LeanFormal.IUT.XiFPaper.S3041S3030IntegrationActual
open LeanFormal.IUT.XiFPaper.S3030AffineOriginClassification
open LeanFormal.IUT.XiFPaper.S2888OriginPreservingOrderTwo
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3054ProjectiveTransport

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

abbrev R0 : Type := S3030AffineOriginClassification.R0

/-- Chart-Z restriction data for a scheme automorphism β of S2844X: an affine
ring automorphism φ of R0 which is K-linear, order two, fixes X, and makes the
chart-Z square commute. -/
structure S3054ChartZRestriction
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X) where
  φ : R0 ≃+* R0
  hk : ∀ a : S2844D6F6BaseChangeActual.K,
    φ (S3030KMap a) = S3030KMap a
  hφ2 : φ.toRingHom.comp φ.toRingHom = RingHom.id R0
  hX : φ (S2801E37X S2844D6F6BaseChangeActual.K) =
    S2801E37X S2844D6F6BaseChangeActual.K
  hsquare : S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ β.left =
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      S2820E37ChartZMap S2844D6F6BaseChangeActual.K

/-- Gluing data: the chart-Z restriction determines β, with the two affine
branches mapping to id and alphaOverS2844. -/
def S3054GluingData : Prop :=
  ∀ (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X),
    S3054ChartZRestriction β →
      ((∀ r : S3054ChartZRestriction β,
          r.φ.toRingHom = RingHom.id R0 →
            β = 𝟙 S2844D6F6BaseChangeActual.S2844X) ∧
       (∀ r : S3054ChartZRestriction β,
          r.φ.toRingHom =
            S2853E37NegationAutomorphismActual.S2853RingHom
              S2844D6F6BaseChangeActual.K →
            β = alphaOverS2844))

/-- The exact projective transport target: S2888 origin-preserving order-two
classification. -/
def S3054ProjectiveTransportTarget : Prop :=
  S2888OriginPreservingOrderTwoClassification

/-- Conditional projective classification from chart-Z restriction data and
gluing. -/
theorem S3054_classification_of_restriction_and_gluing
    (hglue : S3054GluingData)
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (hβ : β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X)
    (horg : S2888OriginPreserving β)
    (r : S3054ChartZRestriction β) :
    β = 𝟙 S2844D6F6BaseChangeActual.S2844X ∨ β = alphaOverS2844 := by
  rcases S3053_affine_classification r.φ r.hk r.hφ2 r.hX with hid | halpha
  · exact Or.inl ((hglue β r).1 r hid)
  · exact Or.inr ((hglue β r).2 r halpha)

/-- The S2888 target from the same data. -/
theorem S3054_projective_transport_of_data
    (hrestrict : ∀ (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X),
      β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X →
      S2888OriginPreserving β → S3054ChartZRestriction β)
    (hglue : S3054GluingData) :
    S3054ProjectiveTransportTarget := by
  intro β hβ horg
  exact S3054_classification_of_restriction_and_gluing hglue β hβ horg
    (hrestrict β hβ horg)

/-!
## Exact target / required chart-Z restriction lemma / first error

Target: S3054ProjectiveTransportTarget = S2888OriginPreservingOrderTwoClassification.

Actual pieces:
* S3054ChartZRestriction: the exact data needed from β, including the chart-Z
  commuting square with S2820E37ChartZMap and the affine ring automorphism φ;
* S3054GluingData: exact two-branch gluing statement;
* S3054_classification_of_restriction_and_gluing: ACTUAL, uses the unconditional
  S3053_affine_classification to split φ into id/alpha and then applies gluing;
* S3054_projective_transport_of_data: ACTUAL conditional on restriction + gluing.

First errors / missing lemmas:
1. S3054ChartZRestriction does not exist for arbitrary β: there is no theorem
   that an order-two origin-preserving scheme automorphism of the glued
   projective S2844X preserves the chart-Z open S2801E37AffineScheme, nor that
   it restricts to a K-linear ring automorphism of R0.
2. S3054GluingData is not proved: no theorem reconstructs β from its chart-Z
   restriction, and no comparison between Spec.map of the affine id/alpha and
   the global 𝟙/alphaOverS2844.  The existing S2858AlphaOverActual provides
   alphaOverS2844 itself, but not the reverse gluing uniqueness for arbitrary β.

No chart restriction or gluing is faked.
-/

#check S3054ChartZRestriction
#check S3054GluingData
#check S3054ProjectiveTransportTarget
#check S3054_classification_of_restriction_and_gluing
#check S3054_projective_transport_of_data
#print axioms S3054_classification_of_restriction_and_gluing
#print axioms S3054_projective_transport_of_data

end LeanFormal.IUT.XiFPaper.S3054ProjectiveTransport
end
