import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientFreeAction
import LeanFormal.IUT.Foundations.Geometry.CurveEtaleFundamentalGroup

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

/-!
# Affine finite-etale quotient cover consumer

The transport-facing structure is already defined in
`ABCBridge.FiniteEtaleQuotientFreeAction`; this file consumes it (no duplicate
structure) and exposes the regular fixed-point quotient cover.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open LeanFormal.IUT.Foundations.Geometry
open ABCBridge.FiniteEtaleQuotientFreeAction

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineFiniteEtaleQuotientCover

universe u

variable (R : Type u) [CommRing R] (G : Type u) [Group G] [Fintype G]

abbrev A : Type u := G → R

abbrev Q : AffineFiniteEtaleQuotientCover R G :=
  regularAffineFiniteEtaleQuotientCover (R := R) (G := G)

theorem Q_cover : (Q R G).cover = regularPermutationCover (R := R) (G := G) := rfl

theorem Q_quotientCover :
    (Q R G).quotientCover = regularQuotientCover (R := R) (G := G) := rfl

theorem Q_carrier :
    finiteEtaleCoverScheme (Q R G).quotientCover =
      Spec (CommRingCat.of (FixedPoints.subalgebra R (G → R) G)) := rfl

theorem Q_structureMap :
    finiteEtaleCoverStructure (Q R G).quotientCover =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (FixedPoints.subalgebra R (G → R) G))) := rfl

theorem Q_etale : Algebra.Etale R (FixedPoints.subalgebra R (G → R) G) :=
  (Q R G).quotient_etale

theorem Q_finite : Module.Finite R (FixedPoints.subalgebra R (G → R) G) :=
  (Q R G).quotient_finite

end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineFiniteEtaleQuotientCover

end