import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientFreeAction
import LeanFormal.IUT.Foundations.AlgebraicGeometry.RegularPermutationQuotientEquivalence
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineFiniteEtaleQuotientConsumer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.RegularPermutationQuotientInstance

/-!
# Regular permutation quotient consumer

Consumes the green regular permutation quotient equivalence, the affine
finite-etale quotient consumer, and the regular permutation instance.  It
packages the actual quotient cover, chart map, cocone IsColimit desc/fac/uniq,
affine finite-etale quotient, section algebra equivalence, and the cover-level
projection.  No residual data and no fabricated quotient are introduced.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace ABCBridge.FiniteEtaleQuotientFreeActionConsumer

universe u

open ABCBridge.FiniteEtaleQuotientFreeAction
open ABCBridge.RegularPermutationQuotientEquivalence
open ABCBridge.AffineFiniteEtaleQuotientConsumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration
open LeanFormal.IUT.Foundations.AlgebraicGeometry.RegularPermutationQuotientInstance
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable (R : Type u) [CommRing R]
variable (G : Type u) [Group G] [Fintype G]

/-- Complete actual consumer package for the regular permutation quotient. -/
structure RegularPermutationQuotientConsumerData where
  quotientCocone : Cocone (RegularPermutationCoconeUniqueness.actionFunctor R G)
  isColimit : IsColimit quotientCocone
  permutationCover : FiniteEtaleCover (Spec (CommRingCat.of R))
  quotientCover : FiniteEtaleCover (Spec (CommRingCat.of R))
  chartMap : permutationCover ⟶ quotientCover
  sectionsEquiv : Γ(permutationCover.carrier, ⊤) ≃+* (G → R)
  affineQuotient : AffineFiniteEtaleQuotient (R := R) (G := G) (A := (G → R))
  coverProjection : permutationCover.carrier ⟶ quotientCover.carrier
  coverProjection_eq_chartMap : coverProjection = chartMap.hom.left

/-- The actual regular permutation quotient consumer package. -/
noncomputable def regularPermutationQuotientConsumerData :
    RegularPermutationQuotientConsumerData R G where
  quotientCocone := regularQuotientCocone (R := R) (G := G)
  isColimit := regularQuotientCocone_isColimit (R := R) (G := G)
  permutationCover := regularPermutationCover (R := R) (G := G)
  quotientCover := regularQuotientCover (R := R) (G := G)
  chartMap := regularQuotientChartMap (R := R) (G := G)
  sectionsEquiv := regularPermutationSectionsRingEquiv (R := R) (G := G)
  affineQuotient := regularAffineFiniteEtaleQuotientPackage (R := R) (G := G)
  coverProjection := (regularQuotientChartMap (R := R) (G := G)).hom.left
  coverProjection_eq_chartMap := rfl

namespace RegularPermutationQuotientConsumerData

variable {R G} (D : RegularPermutationQuotientConsumerData R G)

/-- The desc map of an arbitrary cocone. -/
noncomputable def desc
    (c : Cocone (RegularPermutationCoconeUniqueness.actionFunctor R G)) :
    D.quotientCocone.pt ⟶ c.pt :=
  D.isColimit.desc c

/-- The desc map factors the cocone component. -/
theorem desc_fac
    (c : Cocone (RegularPermutationCoconeUniqueness.actionFunctor R G))
    (j : SingleObj G) :
    D.quotientCocone.ι.app j ≫ D.desc c = c.ι.app j :=
  D.isColimit.fac c j

/-- The desc map is unique. -/
theorem desc_uniq
    (c : Cocone (RegularPermutationCoconeUniqueness.actionFunctor R G))
    (m : D.quotientCocone.pt ⟶ c.pt)
    (hm : ∀ j : SingleObj G, D.quotientCocone.ι.app j ≫ m = c.ι.app j) :
    m = D.desc c :=
  D.isColimit.uniq c m hm

/-- The section algebra equivalence is actual. -/
theorem sectionsEquiv_actual :
    Nonempty (Γ(D.permutationCover.carrier, ⊤) ≃+* (G → R)) :=
  ⟨D.sectionsEquiv⟩

/-- The affine finite-etale quotient is the fixed-point quotient package. -/
theorem affineQuotient_projection :
    D.affineQuotient.projection =
      affineQuotientProjection (R := R) (G := G) (G → R) :=
  D.affineQuotient.projection_eq

/-- The cover-level projection is the chart map underlying morphism. -/
theorem coverProjection_chartMap :
    D.coverProjection = D.chartMap.hom.left :=
  D.coverProjection_eq_chartMap

end RegularPermutationQuotientConsumerData

/-- Complete consumer theorem: actual quotient cover, cocone desc/fac/uniq,
affine finite-etale quotient, sections equivalence, and cover-level projection. -/
theorem regularPermutationQuotientConsumer_complete
    (c : Cocone (RegularPermutationCoconeUniqueness.actionFunctor R G))
    (j : SingleObj G) :
    let D := regularPermutationQuotientConsumerData (R := R) (G := G)
    (Nonempty (D.permutationCover.carrier ≅ Spec (CommRingCat.of (G → R)))) ∧
      (D.quotientCocone.ι.app j ≫ D.isColimit.desc c = c.ι.app j) ∧
      (Nonempty (Γ(D.permutationCover.carrier, ⊤) ≃+* (G → R))) ∧
      (D.coverProjection = D.chartMap.hom.left) := by
  intro D
  refine ⟨?iso, ?fac, ?sections, ?proj⟩
  · exact ⟨Iso.refl _⟩
  · exact D.isColimit.fac c j
  · exact D.sectionsEquiv_actual
  · exact D.coverProjection_chartMap

end ABCBridge.FiniteEtaleQuotientFreeActionConsumer
