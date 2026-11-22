import tmp.sheaf.xif.paper.S3061BranchFactorization
import tmp.sheaf.xif.paper.S3058ChartZPreservation
import tmp.sheaf.xif.paper.S2822PointRealizationRouteActual
import tmp.sheaf.xif.paper.S2831E37InfinityNotOverlapActual
import tmp.sheaf.xif.paper.S2845cZeroPreimageActual
import tmp.sheaf.xif.paper.S2888OriginPreservingOrderTwo

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3061BranchFactorization
open LeanFormal.IUT.XiFPaper.S3058ChartZPreservation
open LeanFormal.IUT.XiFPaper.S2888OriginPreservingOrderTwo
open LeanFormal.IUT.XiFPaper.S2822PointRealizationRouteActual
open LeanFormal.IUT.XiFPaper.S2831E37InfinityNotOverlapActual
open LeanFormal.IUT.XiFPaper.S2845cZeroPreimageActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3062ChartZPreservationProof

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

abbrev K := S2844D6F6BaseChangeActual.K
abbrev G := E37ProjGluedScheme K (S2820E37TransitionIso K)

noncomputable def S3062InfinityPoint : G :=
  E37ProjChartYMap K (S2820E37TransitionIso K) (E37InfinityPoint K)

/-- Exact glue-data lemma: chart-Y points outside the overlap range are the
infinity point. -/
def S3062ChartYNonoverlapInfinity : Prop :=
  ∀ y : E37ChartYScheme K,
    y ∉ Set.range (E37ChartYOverlapMap K) → y = E37InfinityPoint K

/-- Exact transition lemma: every chart-Y point in the overlap has a chart-Z
preimage in the glued scheme. -/
def S3062ChartYOverlapPreimage : Prop :=
  ∀ y : E37ChartYScheme K, y ∈ Set.range (E37ChartYOverlapMap K) →
    ∃ z : S2801E37AffineScheme K,
      E37ProjChartZMap K (S2820E37TransitionIso K) z =
        E37ProjChartYMap K (S2820E37TransitionIso K) y

/-- Point realization outside infinity: every point other than infinity is in
the chart-Z image. -/
def S3062PointRealization : Prop :=
  ∀ x : G, x ≠ S3062InfinityPoint →
    ∃ z : S2801E37AffineScheme K,
      E37ProjChartZMap K (S2820E37TransitionIso K) z = x

/-- Actual point realization from the two exact glue-data lemmas. -/
theorem S3062_pointRealization_of_glue
    (hnon : S3062ChartYNonoverlapInfinity)
    (hover : S3062ChartYOverlapPreimage) :
    S3062PointRealization := by
  intro x hx
  let D : Scheme.GlueData.{0} := E37ProjGlueData K (S2820E37TransitionIso K)
  obtain ⟨i, y, hy⟩ := D.openCover.exists_eq x
  rcases i with ⟨b⟩
  cases b
  · refine ⟨y, ?_⟩
    rw [show E37ProjChartZMap K (S2820E37TransitionIso K) =
      D.ι (ULift.up false) from rfl]
    rwa [← Scheme.GlueData.openCover_f]
  · by_cases hmem : y ∈ Set.range (E37ChartYOverlapMap K)
    · rcases hover y hmem with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      rw [hz]
      rw [show E37ProjChartYMap K (S2820E37TransitionIso K) =
        D.ι (ULift.up true) from rfl]
      rwa [← Scheme.GlueData.openCover_f]
    · exfalso
      have hyinf : y = E37InfinityPoint K := hnon y hmem
      apply hx
      rw [← hy, hyinf]
      rfl

/-- Infinity is not in the chart-Z image (point form), from S2845c. -/
def S3062InfinityNotInChartZ : Prop :=
  ¬ ∃ z : S2801E37AffineScheme K,
    E37ProjChartZMap K (S2820E37TransitionIso K) z = S3062InfinityPoint

/-- β fixes infinity at underlying-scheme level. -/
def S3062InfinityFixed
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X) : Prop :=
  (S2844InfinityOver).left ≫ β.left = (S2844InfinityOver).left

theorem S3062_infinityFixed_of_origin
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (horg : S2888OriginPreserving β) : S3062InfinityFixed β := by
  unfold S3062InfinityFixed S2888OriginPreserving at *
  exact congrArg (fun f => Over.Hom.left f) horg

/-- Exact chart-Z factorization. -/
def S3062ChartZFactorization
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X) : Prop :=
  ∃ z : S2801E37AffineScheme K ⟶ S2801E37AffineScheme K,
    E37ProjChartZMap K (S2820E37TransitionIso K) ≫ β.left =
      z ≫ E37ProjChartZMap K (S2820E37TransitionIso K)

/-- Exact target: every ∞-fixing order-two automorphism preserves chart-Z. -/
def S3062ChartZFactorizationTarget : Prop :=
  ∀ β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X,
    β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X →
    S3062InfinityFixed β → S3062ChartZFactorization β

/-- The open-immersion factorization input: forgetting points, if β maps the
complement of infinity into itself then ChartZMap ≫ β factors through
ChartZMap. -/
def S3062OpenImmersionFactorization : Prop :=
  ∀ (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X),
    (∀ x : G, x ≠ S3062InfinityPoint → β.left x ≠ S3062InfinityPoint) →
      S3062ChartZFactorization β

/-!
## Exact statements and first error

Actual:
* S3062_pointRealization_of_glue: the two exact glue-data lemmas
  (S3062ChartYNonoverlapInfinity + S3062ChartYOverlapPreimage) give point
  realization outside infinity, via the S2822 two-chart cover.
* S3062_infinityFixed_of_origin.

Exact missing glue-data lemmas:
1. S3062ChartYNonoverlapInfinity: U_Y \ overlap = {infinity}.  Route:
   overlap = basicOpen (tbar K); if y not in overlap then tbar ∈ y.asIdeal;
   the chart-Y relation sbar^3 = sbar tbar^2 + tbar + tbar^2 gives sbar ∈
   y.asIdeal; hence y.asIdeal contains (sbar,tbar) = E37InfinityIdeal, and
   maximality forces y = infinity.  Not yet formalized.
2. S3062ChartYOverlapPreimage: transition from overlap to chart-Z preimage in
   the glued scheme.  Follows from GlueData.ι_eq_iff / transition map, but not
   yet packaged.

Then S3062OpenImmersionFactorization is still missing: point inclusion
β(U_Z)⊆U_Z gives z by the universal property of the chart-Z open immersion.
S2845c S2845_no_chartZ is actual and available; S2845b is not imported (no
olean).  No chart-Z factorization or point realization is faked.
-/

#check S3062ChartYNonoverlapInfinity
#check S3062ChartYOverlapPreimage
#check S3062PointRealization
#check S3062_pointRealization_of_glue
#check S3062InfinityNotInChartZ
#check S3062InfinityFixed
#check S3062_infinityFixed_of_origin
#check S3062ChartZFactorization
#check S3062ChartZFactorizationTarget
#check S3062OpenImmersionFactorization
#print axioms S3062_pointRealization_of_glue
#print axioms S3062_infinityFixed_of_origin

end LeanFormal.IUT.XiFPaper.S3062ChartZPreservationProof
end
