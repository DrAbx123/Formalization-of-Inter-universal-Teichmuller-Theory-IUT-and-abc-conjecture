import tmp.sheaf.xif.paper.S3067PointRealizationActual
import tmp.sheaf.xif.paper.S3062ChartZPreservationProof
import tmp.sheaf.xif.paper.S2820E37TransitionActual
import tmp.sheaf.xif.paper.S2801E37ProjectiveClosure
import tmp.sheaf.xif.paper.S2801D6FaithfulActual
import tmp.sheaf.xif.paper.S2809E6FiniteActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3067PointRealizationActual
open LeanFormal.IUT.XiFPaper.S3062ChartZPreservationProof
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3068OpenImmersionFactorizationActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

abbrev e := S2820E37TransitionIso S2844D6F6BaseChangeActual.K
abbrev D : Scheme.GlueData.{0} :=
  E37ProjGlueData S2844D6F6BaseChangeActual.K e
abbrev ChartZ : S2801E37AffineScheme S2844D6F6BaseChangeActual.K ⟶ D.glued :=
  E37ProjChartZMap S2844D6F6BaseChangeActual.K e

theorem S3068_chartZ_isOpenImmersion : IsOpenImmersion ChartZ := by
  have h := D.ι_isOpenImmersion (ULift.up false)
  simpa [ChartZ, D, E37ProjChartZMap, E37ProjGlueData, E37ProjF, E37ProjU] using h

/-- Actual open-immersion lift for an arbitrary endomorphism βs of the glued
scheme, assuming its chart-Z range is contained in chart-Z. -/
noncomputable def S3068_lift
    (βs : D.glued ⟶ D.glued)
    (H : Set.range (ChartZ ≫ βs) ⊆ Set.range ChartZ) :
    S2801E37AffineScheme S2844D6F6BaseChangeActual.K ⟶
      S2801E37AffineScheme S2844D6F6BaseChangeActual.K :=
  haveI := S3068_chartZ_isOpenImmersion
  IsOpenImmersion.lift ChartZ (ChartZ ≫ βs) H

/-- Actual factorization for βs from the range inclusion. -/
theorem S3068_lift_fac
    (βs : D.glued ⟶ D.glued)
    (H : Set.range (ChartZ ≫ βs) ⊆ Set.range ChartZ) :
    ChartZ ≫ βs = S3068_lift βs H ≫ ChartZ := by
  haveI := S3068_chartZ_isOpenImmersion
  exact (IsOpenImmersion.lift_fac ChartZ (ChartZ ≫ βs) H).symm

/-- Exact type bridge needed to identify β.left with an endomorphism of the
glued scheme. -/
def S3068OverLeftBridge : Prop :=
  Over.left S2844D6F6BaseChangeActual.S2844X =
    E37ProjGluedScheme S2844D6F6BaseChangeActual.K e

/-- Actual type bridge: the underlying scheme of S2844X is the glued E37
scheme. -/
theorem S3068_bridge : S3068OverLeftBridge := rfl

/-- Exact β point-preimage lemma. -/
def S3068BetaPreimageInfinity : Prop :=
  ∀ (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X),
    β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X →
    (∀ x : S3062ChartZPreservationProof.G,
      x ≠ S3062InfinityPoint → β.left x ≠ S3062InfinityPoint) →
    ∀ x : S3062ChartZPreservationProof.G,
      β.left x = S3062InfinityPoint → x = S3062InfinityPoint

/-!
## Exact statements and first error

Actual:
* S3068_chartZ_isOpenImmersion;
* S3068_lift and S3068_lift_fac: for an arbitrary endomorphism βs of the
  glued scheme, if Set.range (ChartZ ≫ βs) ⊆ Set.range ChartZ then ChartZ ≫ βs
  factors through ChartZ via IsOpenImmersion.lift/lift_fac.  The H argument is
  exactly the range inclusion, not a pointwise function application.

First errors:
1. S3068OverLeftBridge: need
   Over.left S2844X = E37ProjGluedScheme K e
   (equivalently S2844X = S2821AsOver K with Over.mk unfolded).  Without it
   β.left cannot be re-typed as βs : D.glued ⟶ D.glued, so S3062ChartZFactorization β
   cannot yet be derived from S3068_lift_fac.
2. S3068BetaPreimageInfinity: β automorphism order two gives point injectivity;
   combined with ∞-fixing this yields β(x)=∞ ⇒ x=∞, but the point-map packaging
   is not formalized.
No factorization or point preimage is faked.
-/

#check S3068_chartZ_isOpenImmersion
#check S3068_lift
#check S3068_lift_fac
#check S3068_bridge
#check S3068OverLeftBridge
#check S3068BetaPreimageInfinity
#print axioms S3068_chartZ_isOpenImmersion
#print axioms S3068_bridge
#print axioms S3068_lift_fac

end LeanFormal.IUT.XiFPaper.S3068OpenImmersionFactorizationActual
end
