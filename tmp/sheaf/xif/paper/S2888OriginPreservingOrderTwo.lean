import tmp.sheaf.xif.paper.S2881OrderTwoClassificationAudit
import tmp.sheaf.xif.paper.S2858AlphaOverActual
import tmp.sheaf.xif.paper.S2844D6F6BaseChangeActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2881OrderTwoClassificationAudit
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2888OriginPreservingOrderTwo

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

/-- Origin-preserving: the endomorphism fixes the point at infinity
S2844InfinityOver : S2844Base ⟶ S2844X. -/
def S2888OriginPreserving
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X) : Prop :=
  S2844InfinityOver ≫ β = S2844InfinityOver

/-- The exact order-two origin-preserving classification target. -/
def S2888OriginPreservingOrderTwoClassification : Prop :=
  ∀ β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X,
    β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X →
    S2888OriginPreserving β →
      β = 𝟙 S2844D6F6BaseChangeActual.S2844X ∨ β = alphaOverS2844

/-- The identity is origin-preserving. -/
theorem S2888_id_originPreserving : S2888OriginPreserving (𝟙 _) := by
  simp [S2888OriginPreserving]

/-- The actual alpha automorphism squares to the identity. -/
theorem S2888_alpha_square :
    alphaOverS2844 ≫ alphaOverS2844 = 𝟙 S2844D6F6BaseChangeActual.S2844X :=
  alphaOverS2844_square

/-!
## First missing for the classification

The statement S2888OriginPreservingOrderTwoClassification is exact and
falsifiable; no proof is provided here.

The first missing object is the affine/origin classification:

  any order-two automorphism of the chart-Z coordinate ring
  S2801E37CoordinateRing K that fixes the base field and corresponds to
  an origin-preserving scheme automorphism is either the identity or the
  chart-Z substitution (x,y) -> (x,-y-1).

Available pieces:
* S2853RingHom and S2853ChartZSchemeEndo give the nontrivial substitution and
  its scheme endomorphism;
* S2858AlphaOverActual proves this glues to alphaOver and squares to id;
* S2858AlphaOverActual/S2856HfOverlapActual prove the chart-Y side fixes the
  structure map and glues.

Missing:
* a theorem that an origin-preserving scheme automorphism preserves the
  chart-Z affine open, hence induces a coordinate-ring automorphism;
* the order-two algebra-automorphism classification for S2801E37CoordinateRing
  over K (including exclusion of translation-like automorphisms, which are
  not origin-preserving but must be ruled out from the affine calculation);
* transport back from the coordinate-ring classification to the glued
  projective scheme.

No classification is faked; only the exact statement and the identity/square
fragments are actual.
-/

#check S2888OriginPreserving
#check S2888OriginPreservingOrderTwoClassification
#check S2888_id_originPreserving
#check S2888_alpha_square
#print axioms S2888_id_originPreserving
#print axioms S2888_alpha_square

end LeanFormal.IUT.XiFPaper.S2888OriginPreservingOrderTwo
end
