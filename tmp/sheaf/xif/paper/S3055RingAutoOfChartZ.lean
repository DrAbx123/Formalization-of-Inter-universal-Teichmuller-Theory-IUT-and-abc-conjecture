import tmp.sheaf.xif.paper.S3054ProjectiveTransport
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3054ProjectiveTransport
open LeanFormal.IUT.XiFPaper.S3030AffineOriginClassification
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0
namespace LeanFormal.IUT.XiFPaper.S3055RingAutoOfChartZ

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual.K :=
  S2847A6.fieldF
local instance : NumberField LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual.K :=
  S2847A6.numberFieldF
local instance : DecidableEq LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual.K :=
  Classical.decEq _

/-- Chart-Z square: z is the affine chart endomorphism induced by β. -/
def S3055ChartZSquare
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (z : S2801E37AffineScheme S2844D6F6BaseChangeActual.K ⟶
      S2801E37AffineScheme S2844D6F6BaseChangeActual.K) : Prop :=
  S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ β.left =
    z ≫ S2820E37ChartZMap S2844D6F6BaseChangeActual.K

/-- Exact ring-automorphism data extracted from the chart-Z restriction. -/
structure S3055RingAutoOfChartZ
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X) where
  z : S2801E37AffineScheme S2844D6F6BaseChangeActual.K ⟶
    S2801E37AffineScheme S2844D6F6BaseChangeActual.K
  φ : S3030AffineOriginClassification.R0 ≃+* S3030AffineOriginClassification.R0
  hz : z = Spec.map (CommRingCat.ofHom φ.toRingHom)
  hk : ∀ a : S2844D6F6BaseChangeActual.K,
    φ (S3030KMap a) = S3030KMap a
  hφ2 : φ.toRingHom.comp φ.toRingHom =
    RingHom.id S3030AffineOriginClassification.R0
  hX : φ (S2801E37X S2844D6F6BaseChangeActual.K) =
    S2801E37X S2844D6F6BaseChangeActual.K
  hsquare : S3055ChartZSquare β z

/-- The S3055 data yields the S3054 chart-Z restriction. -/
noncomputable def S3055_toChartZRestriction
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (D : S3055RingAutoOfChartZ β) : S3054ChartZRestriction β where
  φ := D.φ
  hk := D.hk
  hφ2 := D.hφ2
  hX := D.hX
  hsquare := by
    rw [← D.hz]
    exact D.hsquare

/-!
## Exact statement and first error

S3055RingAutoOfChartZ is the exact data: a chart-Z endomorphism z, a ring
automorphism φ of R0 with z = Spec.map φ, K-linearity, φ^2=1, φ(X)=X, and the
chart-Z square.

Actual: S3055_toChartZRestriction transports the data to S3054.

First error: there is no construction of S3055RingAutoOfChartZ from an
order-two origin-preserving β.  Missing:
* a proof that β preserves the chart-Z open S2801E37AffineScheme (so that the
  composite ChartZMap ≫ β factors through ChartZMap);
* extraction of z from that factorization, and of φ from z via an affine
  equivalence Spec (R0) ≅ S2801E37AffineScheme;
* K-linearity and φ(X)=X for the extracted φ.
No restriction is faked.
-/

#check S3055ChartZSquare
#check S3055RingAutoOfChartZ
#check S3055_toChartZRestriction
#print axioms S3055_toChartZRestriction

end LeanFormal.IUT.XiFPaper.S3055RingAutoOfChartZ
end
