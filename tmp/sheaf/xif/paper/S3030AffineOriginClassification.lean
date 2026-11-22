import tmp.sheaf.xif.paper.S2897ValuationInputActual
import tmp.sheaf.xif.paper.S2853E37NegationAutomorphismActual
import tmp.sheaf.xif.paper.S2858AlphaSquareActual
import tmp.sheaf.xif.paper.S2801D6FaithfulActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2897ValuationInputActual
open LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual
open LeanFormal.IUT.XiFPaper.S2858AlphaSquareActual
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3030AffineOriginClassification

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

abbrev R0 : Type := S2801E37CoordinateRing S2844D6F6BaseChangeActual.K

/-- The K-scalar image in R0, written without an Algebra instance. -/
noncomputable def S3030KMap (a : S2844D6F6BaseChangeActual.K) : R0 :=
  Ideal.Quotient.mk (S2801E37Ideal S2844D6F6BaseChangeActual.K)
    (MvPolynomial.C a)

/-- Affine origin-preserving order-two classification on chart Z: an order-two
ring automorphism of the E37 coordinate ring which fixes the origin coordinate
X is either the identity or the chart-Z alpha substitution
(x,y) -> (x,-y-1). -/
def S3030AffineOriginClassification : Prop :=
  ∀ φ : R0 ≃+* R0,
    (∀ a : S2844D6F6BaseChangeActual.K,
      φ (S3030KMap a) = S3030KMap a) →
    φ.toRingHom.comp φ.toRingHom = RingHom.id R0 →
    φ (S2801E37X S2844D6F6BaseChangeActual.K) =
      S2801E37X S2844D6F6BaseChangeActual.K →
      φ = RingHom.id R0 ∨
        φ = S2853RingHom S2844D6F6BaseChangeActual.K

/-- Actual involution of the alpha substitution. -/
theorem S3030_alpha_comp_self :
    (S2853RingHom S2844D6F6BaseChangeActual.K).comp
        (S2853RingHom S2844D6F6BaseChangeActual.K) =
      RingHom.id R0 :=
  S2853RingHom_comp_self S2844D6F6BaseChangeActual.K

/-- The identity branch. -/
theorem S3030_id_mem :
    (RingHom.id R0 = RingHom.id R0) ∨
      (RingHom.id R0 = S2853RingHom S2844D6F6BaseChangeActual.K) :=
  Or.inl rfl

/-- The alpha branch. -/
theorem S3030_alpha_mem :
    (S2853RingHom S2844D6F6BaseChangeActual.K = RingHom.id R0) ∨
      (S2853RingHom S2844D6F6BaseChangeActual.K =
        S2853RingHom S2844D6F6BaseChangeActual.K) :=
  Or.inr rfl

/-!
## Exact target and first error

S3030AffineOriginClassification is the affine chart-Z classification:

  φ^2 = id and φ(X) = X  =>  φ = id or φ = S2853RingHom,

where S2853RingHom is the actual substitution (x,y) -> (x,-y-1).

Actual:
* S3030_alpha_comp_self: the alpha substitution is an involution
  (S2853RingHom_comp_self);
* S2897/S2896 provide the conditional phi(X)=X from valuation/XFixed input;
  it is not used as an actual theorem here because the Algebra instance is not
  available in this file;
* S3030_id_mem / S3030_alpha_mem record the two branches.

First error: the algebra classification itself is not proved.  In particular:
* no theorem classifies order-two K-algebra automorphisms of the E37
  coordinate ring;
* no theorem excludes translation-like substitutions y -> y + t: origin
  preservation gives only φ(X)=X, which fixes the x-coordinate but does not by
  itself force t=0 without the order-two polynomial computation;
* no theorem transports an affine coordinate-ring classification back to the
  glued projective scheme (S2888/S3028).

S2982_rigidity is a 2-categorical statement about strong transformations; it
does not classify scheme or coordinate-ring automorphisms.  No classification is
faked.
-/

#check S3030AffineOriginClassification
#check S3030_alpha_comp_self
#check S3030_id_mem
#check S3030_alpha_mem
#print axioms S3030_alpha_comp_self

end LeanFormal.IUT.XiFPaper.S3030AffineOriginClassification
end
