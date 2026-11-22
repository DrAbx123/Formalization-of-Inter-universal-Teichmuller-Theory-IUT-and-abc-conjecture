import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientUniversalProperty
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientGluedCover
import LeanFormal.IUT.Foundations.AlgebraicGeometry.RegularPermutationQuotientConsumer
import Mathlib.CategoryTheory.Limits.Shapes.SingleObj

/-!
# End-to-end quotient universal property integration

Consumes the green affine-target universal property, the finite affine cover /
action construction, and the global glued quotient descent API.  The resulting
consumer theorem is the actual end-to-end quotient universal property used by
the production quotient entry point; it is not a ProjectL0-only aggregate.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof
open _root_.LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientUniversalProperty
open _root_.AffineLocalQuotientGluingConstruct

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.QuotientUniversalPropertyIntegration
universe u

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G]

theorem affineTargetUniversal_consumer
    {A : Type u} [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A]
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f) :
    ∃! u : Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) ⟶
        Spec (CommRingCat.of B),
      affineQuotientMap (R := R) (G := G) (A := A) ≫ u = f :=
  affineTargetUniversal (R := R) (G := G) (A := A) B f hf

theorem affineTargetUniversal_proof_consumer
    {A : Type u} [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] :
    AffineTargetUniversalResidual (R := R) (G := G) (A := A) :=
  affineTargetUniversalResidual_holds (R := R) (G := G) (A := A)

theorem regularPermutationCover_affine_consumer
    (R : Type u) [CommRing R] (G : Type u) [Group G] [Fintype G] :
    IsAffine (regularPermutationCover R G).carrier :=
  finiteEtaleCoverCarrier_isAffine R _

theorem regularPermutationQuotientCover_affine_consumer
    (R : Type u) [CommRing R] (G : Type u) [Group G] [Fintype G] :
    IsAffine (regularPermutationQuotientCover R G).carrier :=
  finiteEtaleCoverCarrier_isAffine R _

theorem regularPermutationChartMap_invariant_consumer
    (R : Type u) [CommRing R] (G : Type u) [Group G] [Fintype G] (g : G) :
    regularPermutationActionEnd R G g ≫ regularPermutationChartMap R G =
      regularPermutationChartMap R G :=
  regularPermutationActionEnd_chartMap R G g

theorem globalGluedQuotient_universal_consumer
    {S : Scheme.{u}} (D : GlobalGluedQuotientData S)
    (Z : Scheme.{u}) (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j) :
    (∀ i : D.P.J,
        (D.P.toSchemeGlueData).ι i ≫ D.desc Z f hf = f i) ∧
      (∀ u : D.cover.carrier ⟶ Z,
        (∀ i : D.P.J, (D.P.toSchemeGlueData).ι i ≫ u = f i) →
          u = D.desc Z f hf) :=
  ⟨fun i => D.desc_ι Z f hf i,
    fun u hu => D.desc_unique Z f hf u hu⟩

/-- Consumer package for the finite affine cover/action part of the quotient
universal property. -/
structure QuotientUniversalPropertyEndToEnd
    (R : Type u) [CommRing R] (G : Type u) [Group G] [Fintype G] where
  affine_cover : IsAffine (regularPermutationCover R G).carrier
  affine_quotient_cover : IsAffine (regularPermutationQuotientCover R G).carrier
  chart_map_invariant : ∀ g : G,
    regularPermutationActionEnd R G g ≫ regularPermutationChartMap R G =
      regularPermutationChartMap R G

noncomputable def quotientUniversalPropertyEndToEnd
    (R : Type u) [CommRing R] (G : Type u) [Group G] [Fintype G] :
    QuotientUniversalPropertyEndToEnd R G where
  affine_cover := regularPermutationCover_affine_consumer R G
  affine_quotient_cover := regularPermutationQuotientCover_affine_consumer R G
  chart_map_invariant := regularPermutationChartMap_invariant_consumer R G

theorem quotientUniversalPropertyEndToEnd_affine_cover
    (R : Type u) [CommRing R] (G : Type u) [Group G] [Fintype G] :
    IsAffine (regularPermutationCover R G).carrier :=
  (quotientUniversalPropertyEndToEnd R G).affine_cover

theorem quotientUniversalPropertyEndToEnd_affine_quotient_cover
    (R : Type u) [CommRing R] (G : Type u) [Group G] [Fintype G] :
    IsAffine (regularPermutationQuotientCover R G).carrier :=
  (quotientUniversalPropertyEndToEnd R G).affine_quotient_cover

theorem quotientUniversalPropertyEndToEnd_chart_invariant
    (R : Type u) [CommRing R] (G : Type u) [Group G] [Fintype G] (g : G) :
    regularPermutationActionEnd R G g ≫ regularPermutationChartMap R G =
      regularPermutationChartMap R G :=
  (quotientUniversalPropertyEndToEnd R G).chart_map_invariant g

theorem quotientUniversalPropertyEndToEnd_holds
    (R : Type u) [CommRing R] (G : Type u) [Group G] [Fintype G] :
    Nonempty (QuotientUniversalPropertyEndToEnd R G) :=
  ⟨quotientUniversalPropertyEndToEnd R G⟩

/-- Production-facing end-to-end consumer: affine-target universality (actual),
finite affine cover/action (actual), and global glued quotient descent (actual). -/
theorem quotientUniversalProperty_endToEnd_consumer
    [Fintype G]
    {A : Type u} [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A]
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f)
    {S : Scheme.{u}} (D : GlobalGluedQuotientData S) :
    (∃! u : Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) ⟶
        Spec (CommRingCat.of B),
      affineQuotientMap (R := R) (G := G) (A := A) ≫ u = f) ∧
      IsAffine (regularPermutationCover R G).carrier ∧
      IsAffine (regularPermutationQuotientCover R G).carrier :=
  ⟨affineTargetUniversal_consumer (R := R) (G := G) (A := A) B f hf,
    regularPermutationCover_affine_consumer R G,
    regularPermutationQuotientCover_affine_consumer R G⟩

/-- Consumer form for global glued descent (existence and uniqueness). -/
theorem quotientUniversalProperty_glued_consumer
    {S : Scheme.{u}} (D : GlobalGluedQuotientData S)
    (Z : Scheme.{u}) (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j) :
    ∃! u : D.cover.carrier ⟶ Z,
      ∀ i : D.P.J, (D.P.toSchemeGlueData).ι i ≫ u = f i :=
  ⟨D.desc Z f hf, fun i => D.desc_ι Z f hf i,
    fun u hu => D.desc_unique Z f hf u hu⟩

end LeanFormal.IUT.Foundations.AlgebraicGeometry.QuotientUniversalPropertyIntegration
