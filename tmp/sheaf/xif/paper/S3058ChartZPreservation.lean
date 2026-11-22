import tmp.sheaf.xif.paper.S3055RingAutoOfChartZ
import tmp.sheaf.xif.paper.S2888OriginPreservingOrderTwo

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3055RingAutoOfChartZ
open LeanFormal.IUT.XiFPaper.S3030AffineOriginClassification
open LeanFormal.IUT.XiFPaper.S2888OriginPreservingOrderTwo
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3058ChartZPreservation

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

/-- Exact target: every order-two origin-preserving scheme auto of S2844X
yields chart-Z affine data S3055RingAutoOfChartZ. -/
def S3058ChartZPreservationTarget : Prop :=
  ∀ β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X,
    β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X →
    S2888OriginPreserving β → Nonempty (S3055RingAutoOfChartZ β)

/-- The exact two equalities needed for the identity branch: the affine
identity's Spec.map comparison and the chart-Z square. -/
structure S3058IdentityChartZData where
  hz : (𝟙 (S2801E37AffineScheme S2844D6F6BaseChangeActual.K)) =
    Spec.map (CommRingCat.ofHom
      (RingEquiv.refl (S3030AffineOriginClassification.R0) : _ ≃+* _).toRingHom)
  hsquare : S3055ChartZSquare (𝟙 S2844D6F6BaseChangeActual.S2844X)
    (𝟙 (S2801E37AffineScheme S2844D6F6BaseChangeActual.K))

/-- Identity branch, actual from the two explicit equalities. -/
noncomputable def S3058_id_ringAuto
    (D : S3058IdentityChartZData) :
    S3055RingAutoOfChartZ (𝟙 S2844D6F6BaseChangeActual.S2844X) where
  z := 𝟙 (S2801E37AffineScheme S2844D6F6BaseChangeActual.K)
  φ := RingEquiv.refl (S3030AffineOriginClassification.R0)
  hz := D.hz
  hk := fun _ => rfl
  hφ2 := rfl
  hX := rfl
  hsquare := D.hsquare

/-!
## Exact target and first error

S3058ChartZPreservationTarget is the exact chart-Z preservation target.

Actual: the identity branch structure S3058_id_ringAuto, given the two explicit
affine identities (hz and the chart-Z square).

First error: no construction for arbitrary order-two origin-preserving β.
Missing:
* chart-Z preservation: ChartZMap ≫ β.left factors through ChartZMap;
* extraction of z : Spec R0 → Spec R0 and φ : R0 ≃+* R0 from that factorization;
* K-linearity, φ(X)=X, φ²=1 for the extracted φ.
No chart-Z restriction is faked.
-/

#check S3058ChartZPreservationTarget
#check S3058IdentityChartZData
#check S3058_id_ringAuto
#print axioms S3058_id_ringAuto

end LeanFormal.IUT.XiFPaper.S3058ChartZPreservation
end
