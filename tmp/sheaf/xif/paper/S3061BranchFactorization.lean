import tmp.sheaf.xif.paper.S3060ChartZFromOriginToChart
import tmp.sheaf.xif.paper.S3058ChartZPreservation
import tmp.sheaf.xif.paper.S3055RingAutoOfChartZ

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3060ChartZFromOriginToChart
open LeanFormal.IUT.XiFPaper.S3058ChartZPreservation
open LeanFormal.IUT.XiFPaper.S3055RingAutoOfChartZ
open LeanFormal.IUT.XiFPaper.S2888OriginPreservingOrderTwo
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S3030AffineOriginClassification
open LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3061BranchFactorization

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

/-- The two branches of the correction: identity or alpha. -/
inductive S3061Branch
  | id
  | alpha
  deriving DecidableEq, Repr

/-- Branch-dependent chart-Z factorization data. -/
structure S3061BranchFactor
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (b : S3061Branch) where
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

/-- The corrected branch-dependent factorization target. -/
def S3061BranchFactorizationTarget : Prop :=
  ∀ β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X,
    β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X →
    S2888OriginPreserving β →
      ∃ b : S3061Branch, Nonempty (S3061BranchFactor β b)

/-- A branch factor yields S3055RingAutoOfChartZ. -/
noncomputable def S3061_toS3055
    {β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X}
    {b : S3061Branch} (D : S3061BranchFactor β b) : S3055RingAutoOfChartZ β where
  z := D.z
  φ := D.φ
  hz := D.hz
  hk := D.hk
  hφ2 := D.hφ2
  hX := D.hX
  hsquare := D.hsquare

/-- Identity branch factor, actual from S3058IdentityChartZData. -/
noncomputable def S3061_idFactor
    (D : S3058IdentityChartZData) :
    S3061BranchFactor (𝟙 S2844D6F6BaseChangeActual.S2844X) S3061Branch.id where
  z := 𝟙 (S2801E37AffineScheme S2844D6F6BaseChangeActual.K)
  φ := RingEquiv.refl (S3030AffineOriginClassification.R0)
  hz := D.hz
  hk := fun _ => rfl
  hφ2 := rfl
  hX := rfl
  hsquare := D.hsquare

/-- Alpha branch factor, actual from an S3055 alpha chart-Z datum. -/
noncomputable def S3061_alphaFactor
    (D : S3055RingAutoOfChartZ alphaOverS2844) :
    S3061BranchFactor alphaOverS2844 S3061Branch.alpha where
  z := D.z
  φ := D.φ
  hz := D.hz
  hk := D.hk
  hφ2 := D.hφ2
  hX := D.hX
  hsquare := D.hsquare

/-- The corrected target yields S3058ChartZPreservationTarget, hence the
arbitrary chart-Z branch. -/
theorem S3061_to_S3058
    (h : S3061BranchFactorizationTarget) :
    S3058ChartZPreservationTarget := by
  intro β hβ horig
  rcases h β hβ horig with ⟨b, ⟨D⟩⟩
  exact ⟨S3061_toS3055 D⟩

/-!
## Exact corrected target and first error

S3061BranchFactorizationTarget is the branch-dependent replacement for the
false S2913OriginToChart: for every order-two origin-preserving β, either the
identity branch (z = id) or the alpha branch (z = S2853ChartZSchemeEndo) gives
z, φ, φ(X)=X, φ²=1, K-linearity and the chart-Z square.

Actual:
* S3061_toS3055: a branch factor yields S3055RingAutoOfChartZ;
* S3061_idFactor: identity branch from S3058IdentityChartZData;
* S3061_alphaFactor: alpha branch from an S3055 alpha chart-Z datum.

First error: no proof of S3061BranchFactorizationTarget for arbitrary β.  The
missing geometric fact is exactly the chart-Z restriction giving either z=id or
z=alpha; this is not derivable from β²=1 and origin preservation alone in the
current tree.  No branch is faked.
-/

#check S3061Branch
#check S3061BranchFactor
#check S3061BranchFactorizationTarget
#check S3061_toS3055
#check S3061_idFactor
#check S3061_alphaFactor
#check S3061_to_S3058
#print axioms S3061_toS3055
#print axioms S3061_idFactor
#print axioms S3061_to_S3058

end LeanFormal.IUT.XiFPaper.S3061BranchFactorization
end
