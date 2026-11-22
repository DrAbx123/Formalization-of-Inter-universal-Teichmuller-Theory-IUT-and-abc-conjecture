import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientFreeActionConsumer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.RegularPermutationQuotientInstance

/-!
# Project entry: finite etale quotient in the free action case

Exposes the actual free-action quotient package for the regular permutation
cover: quotient cover, chart map, cocone IsColimit desc/fac/uniq, section
algebra equivalence, affine finite-etale quotient, and cover-level projection.
Consumes the green consumer and instance modules.  No residual is introduced.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace LeanFormal.IUT.ProjectFiniteEtaleQuotientFreeActionEntry

universe u

open ABCBridge.FiniteEtaleQuotientFreeActionConsumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.RegularPermutationQuotientInstance
open ABCBridge.RegularPermutationQuotientEquivalence
open ABCBridge.AffineFiniteEtaleQuotientConsumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable (R : Type u) [CommRing R]
variable (G : Type u) [Group G] [Fintype G]

/-- The Project-facing free-action quotient package. -/
noncomputable def projectFiniteEtaleQuotientFreeActionPackage :
    RegularPermutationQuotientConsumerData R G :=
  regularPermutationQuotientConsumerData (R := R) (G := G)

/-- The actual quotient cover in the Project package. -/
noncomputable def projectFiniteEtaleQuotientFreeActionCover :
    FiniteEtaleCover (Spec (CommRingCat.of R)) :=
  (projectFiniteEtaleQuotientFreeActionPackage R G).quotientCover

/-- The actual quotient chart map in the Project package. -/
noncomputable def projectFiniteEtaleQuotientFreeActionChartMap :
    (projectFiniteEtaleQuotientFreeActionPackage R G).permutationCover ⟶
      (projectFiniteEtaleQuotientFreeActionPackage R G).quotientCover :=
  (projectFiniteEtaleQuotientFreeActionPackage R G).chartMap

/-- The quotient cocone in the Project package. -/
noncomputable def projectFiniteEtaleQuotientFreeActionCocone :
    Cocone (RegularPermutationCoconeUniqueness.actionFunctor R G) :=
  (projectFiniteEtaleQuotientFreeActionPackage R G).quotientCocone

/-- The actual IsColimit proof in the Project package. -/
noncomputable def projectFiniteEtaleQuotientFreeActionCocone_isColimit :
    IsColimit (projectFiniteEtaleQuotientFreeActionCocone R G) :=
  (projectFiniteEtaleQuotientFreeActionPackage R G).isColimit

/-- The desc map of an arbitrary cocone. -/
noncomputable def projectFiniteEtaleQuotientFreeActionDesc
    (c : Cocone (RegularPermutationCoconeUniqueness.actionFunctor R G)) :
    (projectFiniteEtaleQuotientFreeActionCocone R G).pt ⟶ c.pt :=
  (projectFiniteEtaleQuotientFreeActionPackage R G).desc c

/-- The desc map factors every cocone component. -/
theorem projectFiniteEtaleQuotientFreeActionDesc_fac
    (c : Cocone (RegularPermutationCoconeUniqueness.actionFunctor R G))
    (j : SingleObj G) :
    (projectFiniteEtaleQuotientFreeActionCocone R G).ι.app j ≫
        projectFiniteEtaleQuotientFreeActionDesc R G c = c.ι.app j :=
  (projectFiniteEtaleQuotientFreeActionPackage R G).desc_fac c j

/-- The desc map is unique. -/
theorem projectFiniteEtaleQuotientFreeActionDesc_uniq
    (c : Cocone (RegularPermutationCoconeUniqueness.actionFunctor R G))
    (m : (projectFiniteEtaleQuotientFreeActionCocone R G).pt ⟶ c.pt)
    (hm : ∀ j : SingleObj G,
      (projectFiniteEtaleQuotientFreeActionCocone R G).ι.app j ≫ m = c.ι.app j) :
    m = projectFiniteEtaleQuotientFreeActionDesc R G c :=
  (projectFiniteEtaleQuotientFreeActionPackage R G).desc_uniq c m hm

/-- The section algebra equivalence Γ(cover) ≃+* (G → R). -/
theorem projectFiniteEtaleQuotientFreeActionSections :
    Nonempty (Γ((projectFiniteEtaleQuotientFreeActionPackage R G).permutationCover.carrier, ⊤)
      ≃+* (G → R)) :=
  (projectFiniteEtaleQuotientFreeActionPackage R G).sectionsEquiv_actual

/-- The affine finite-etale quotient package is actual. -/
theorem projectFiniteEtaleQuotientFreeActionAffine :
    Nonempty (AffineFiniteEtaleQuotient (R := R) (G := G) (A := (G → R))) :=
  ⟨(projectFiniteEtaleQuotientFreeActionPackage R G).affineQuotient⟩

/-- The cover-level projection is the chart map underlying morphism. -/
theorem projectFiniteEtaleQuotientFreeActionProjection :
    (projectFiniteEtaleQuotientFreeActionPackage R G).coverProjection =
      (projectFiniteEtaleQuotientFreeActionChartMap R G).hom.left :=
  (projectFiniteEtaleQuotientFreeActionPackage R G).coverProjection_chartMap

/-- Complete Project-facing package consumer. -/
theorem projectFiniteEtaleQuotientFreeAction_complete
    (c : Cocone (RegularPermutationCoconeUniqueness.actionFunctor R G))
    (j : SingleObj G) :
    let D := projectFiniteEtaleQuotientFreeActionPackage R G
    (D.chartMap = D.chartMap) ∧
      (D.quotientCocone.ι.app j ≫ D.isColimit.desc c = c.ι.app j) ∧
      (Nonempty (Γ(D.permutationCover.carrier, ⊤) ≃+* (G → R))) ∧
      (D.coverProjection = D.chartMap.hom.left) :=
  ⟨rfl,
    (projectFiniteEtaleQuotientFreeActionPackage R G).isColimit.fac c j,
    (projectFiniteEtaleQuotientFreeActionPackage R G).sectionsEquiv_actual,
    (projectFiniteEtaleQuotientFreeActionPackage R G).coverProjection_chartMap⟩

end LeanFormal.IUT.ProjectFiniteEtaleQuotientFreeActionEntry
