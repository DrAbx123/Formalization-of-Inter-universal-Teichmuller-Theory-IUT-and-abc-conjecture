import LeanFormal.IUT.Foundations.AlgebraicGeometry.QuotientCoverProjection
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
import Mathlib.AlgebraicGeometry.Morphisms.Finite

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.QuotientMapFinite

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry.QuotientCoverProjection
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [Finite G]

variable (X : Scheme.{u}) [IsAffine X] [Algebra R (sections X)]
variable [MulSemiringAction G (sections X)] [SMulCommClass G R (sections X)]

/-- The affine quotient projection is finite. -/
theorem quotientProjection_isFinite [Module.Finite R (sections X)] :
    IsFinite (quotientProjection (R := R) (G := G) X) := by
  unfold quotientProjection
  haveI := affineFixedPointQuotientMap_isFinite (R := R) (A := sections X) (G := G)
  infer_instance

variable (f : X ⟶ Spec (CommRingCat.of R))

/-- The finite projection is over Spec R. -/
theorem quotientProjection_over_spec [Module.Finite R (sections X)]
    (hiso : X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R (sections X))) = f) :
    quotientProjection (R := R) (G := G) X ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (fixedPointSubalgebra R (sections X) G))) = f := by
  unfold quotientProjection
  rw [Category.assoc, affineFixedPointQuotientMap_comp_specMap_algebraMap]
  exact hiso

end LeanFormal.IUT.Foundations.AlgebraicGeometry.QuotientMapFinite
