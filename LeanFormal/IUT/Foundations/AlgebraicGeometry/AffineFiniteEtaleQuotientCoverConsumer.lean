import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineFiniteEtaleQuotientCover
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineFiniteEtaleQuotientConsumer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

/-!
# Consumer of the affine finite-etale quotient cover

Consumes the green `AffineFiniteEtaleQuotientCover` and the production regular
permutation quotient structure.  Exposes the cover-level finite etale facts and
projection consumer, with no residual.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.Foundations.Geometry
open ABCBridge.FiniteEtaleQuotientFreeAction
open ABCBridge.AffineFiniteEtaleQuotientConsumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineFiniteEtaleQuotientCoverConsumer

universe u

variable (R : Type u) [CommRing R] (G : Type u) [Group G] [Fintype G]

abbrev Q : AffineFiniteEtaleQuotientCover R G :=
  regularAffineFiniteEtaleQuotientCover (R := R) (G := G)

theorem cover : (Q R G).cover = regularPermutationCover (R := R) (G := G) := rfl

theorem quotientCover :
    (Q R G).quotientCover = regularQuotientCover (R := R) (G := G) := rfl

theorem cover_etale :
    Etale (finiteEtaleCoverStructure (Q R G).cover) :=
  (Q R G).cover.etale_structureMap

theorem cover_finite :
    IsFinite (finiteEtaleCoverStructure (Q R G).cover) :=
  (Q R G).cover.finite_structureMap

theorem quotientCover_etale :
    Etale (finiteEtaleCoverStructure (Q R G).quotientCover) :=
  (Q R G).quotientCover.etale_structureMap

theorem quotientCover_finite :
    IsFinite (finiteEtaleCoverStructure (Q R G).quotientCover) :=
  (Q R G).quotientCover.finite_structureMap

theorem quotientCover_carrier :
    finiteEtaleCoverScheme (Q R G).quotientCover =
      Spec (CommRingCat.of (FixedPoints.subalgebra R (G → R) G)) := rfl

theorem quotientCover_structureMap :
    finiteEtaleCoverStructure (Q R G).quotientCover =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (FixedPoints.subalgebra R (G → R) G))) := rfl

theorem projection_consumer :
    ∀ g : G,
      specAction (R := R) (G := G) (A := G → R) g ≫
          (regularAffineFiniteEtaleQuotientPackage R G).projection =
        (regularAffineFiniteEtaleQuotientPackage R G).projection :=
  regularAffineFiniteEtaleQuotientProjection_consumer R G

theorem cover_consumer :
    Etale (finiteEtaleCoverStructure (Q R G).quotientCover) ∧
      IsFinite (finiteEtaleCoverStructure (Q R G).quotientCover) ∧
      (∀ g : G, specAction (R := R) (G := G) (A := G → R) g ≫
          (regularAffineFiniteEtaleQuotientPackage R G).projection =
        (regularAffineFiniteEtaleQuotientPackage R G).projection) :=
  ⟨quotientCover_etale R G, quotientCover_finite R G,
    projection_consumer R G⟩

end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineFiniteEtaleQuotientCoverConsumer

end