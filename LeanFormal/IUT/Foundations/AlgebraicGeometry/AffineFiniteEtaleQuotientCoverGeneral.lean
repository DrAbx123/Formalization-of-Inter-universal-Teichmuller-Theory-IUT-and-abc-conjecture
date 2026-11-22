import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientGluedCover
import LeanFormal.IUT.Foundations.Geometry.CurveEtaleFundamentalGroup

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

/-!
# General affine finite-etale quotient cover

For a commutative `R`-algebra `A` with finite group action, the fixed-point
quotient `Spec (A^G)` is an affine finite-etale cover of `Spec R` under the
explicit hypotheses `Algebra.Etale R (A^G)` and `Module.Finite R (A^G)`.
This is the general quotient cover used by the section algebra `A = Γ(X)`.
Unless the regular permutation specialization, no `G → R` structure is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineFiniteEtaleQuotientCoverGeneral

universe u

variable {R : Type u} [CommRing R]

abbrev base : Scheme.{u} := Spec (CommRingCat.of R)

variable {A : Type u} [CommRing A] [Algebra R A]
  {G : Type u} [Group G] [MulSemiringAction G A] [SMulCommClass G R A]

abbrev fixedPoints : Subalgebra R A := FixedPoints.subalgebra R A G

abbrev quotientScheme : Scheme.{u} :=
  Spec (CommRingCat.of (FixedPoints.subalgebra R A G))

abbrev quotientStructure :
    quotientScheme (R := R) (A := A) (G := G) ⟶ base (R := R) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap R (FixedPoints.subalgebra R A G)))

/-- The general fixed-point quotient finite-etale cover. -/
noncomputable def affineQuotientCoverGeneral
    (hEt : Algebra.Etale R (FixedPoints.subalgebra R A G))
    (hFin : Module.Finite R (FixedPoints.subalgebra R A G)) :
    FiniteEtaleCover (base (R := R)) :=
  FiniteEtaleCover.mk (quotientStructure (R := R) (A := A) (G := G))
    (specMap_etale_of_algebra_etale (R := R) hEt)
    (specMap_finite_of_module_finite (R := R) hFin)

theorem affineQuotientCoverGeneral_carrier
    (hEt : Algebra.Etale R (FixedPoints.subalgebra R A G))
    (hFin : Module.Finite R (FixedPoints.subalgebra R A G)) :
    (affineQuotientCoverGeneral hEt hFin).carrier =
      Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) := rfl

theorem affineQuotientCoverGeneral_structureMap
    (hEt : Algebra.Etale R (FixedPoints.subalgebra R A G))
    (hFin : Module.Finite R (FixedPoints.subalgebra R A G)) :
    (affineQuotientCoverGeneral hEt hFin).structureMap =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (FixedPoints.subalgebra R A G))) := rfl

theorem affineQuotientCoverGeneral_etale
    (hEt : Algebra.Etale R (FixedPoints.subalgebra R A G))
    (hFin : Module.Finite R (FixedPoints.subalgebra R A G)) :
    Etale ((affineQuotientCoverGeneral hEt hFin).structureMap) :=
  (affineQuotientCoverGeneral hEt hFin).etale_structureMap

theorem affineQuotientCoverGeneral_finite
    (hEt : Algebra.Etale R (FixedPoints.subalgebra R A G))
    (hFin : Module.Finite R (FixedPoints.subalgebra R A G)) :
    IsFinite ((affineQuotientCoverGeneral hEt hFin).structureMap) :=
  (affineQuotientCoverGeneral hEt hFin).finite_structureMap

noncomputable def affineQuotientProjection :
    Spec (CommRingCat.of A) ⟶
      Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) :=
  Spec.map (CommRingCat.ofHom
    (Subalgebra.val (FixedPoints.subalgebra R A G)).toRingHom)

end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineFiniteEtaleQuotientCoverGeneral

end