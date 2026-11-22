import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
import LeanFormal.IUT.IUTII.Frobenioid.Example36EtaleCoverFoundations
import Mathlib.AlgebraicGeometry.AffineScheme

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.QuotientCoverProjection

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [Finite G]

abbrev sections (X : Scheme.{u}) : Type u := Γ(X, ⊤)

variable (X : Scheme.{u}) [IsAffine X] [Algebra R (sections X)]
variable [MulSemiringAction G (sections X)] [SMulCommClass G R (sections X)]

/-- The affine projection X -> Spec((Gamma X)^G). -/
noncomputable def quotientProjection :
    X ⟶ Spec (CommRingCat.of (fixedPointSubalgebra R (sections X) G)) :=
  X.isoSpec.hom ≫ affineFixedPointQuotientMap R (sections X) G

end LeanFormal.IUT.Foundations.AlgebraicGeometry.QuotientCoverProjection
