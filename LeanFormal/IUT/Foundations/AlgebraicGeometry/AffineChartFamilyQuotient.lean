import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartFamilyFromCover
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Affine chart family: local quotient from algebra data

This file constructs the actual affine local quotient chart and its map from
explicit coordinate algebra data, using the production general affine G2
consumer. It is the algebra-level half of the missing local-quotient
construction; the action/restriction half is separate.

Post-compile-delta draft; held for watchdog compilation. No provider/IsColimit.
-/

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartFamilyQuotient

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartFamilyFromCover
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDesc
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R G : Type u} [CommRing R] [Group G] [Fintype G] [DecidableEq G]
variable {A : Type u} [CommRing A] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A]
  [Algebra.Etale R A] [Module.Finite R A]

/-- The actual local quotient cover of an affine chart algebra. -/
noncomputable def affineChartQuotientCover :
    FiniteEtaleCover (Spec (CommRingCat.of R)) :=
  affineQuotientCoverGeneral (R := R) A G

/-- The actual chart map from the affine cover to the local quotient. -/
noncomputable def affineChartQuotientMap :
    affineCover (R := R) A inferInstance inferInstance ⟶
      affineChartQuotientCover (R := R) (A := A) (G := G) :=
  affineQuotientCoverMapGeneral (R := R) A G

theorem affineChartQuotientCover_structureMap :
    (affineChartQuotientCover (R := R) (A := A) (G := G)).structureMap =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (fixedPointSubalgebra R A G))) :=
  rfl

theorem affineChartQuotientCover_etale :
    Etale (affineChartQuotientCover (R := R) (A := A) (G := G)).structureMap :=
  (affineChartQuotientCover (R := R) (A := A) (G := G)).etale_structureMap

theorem affineChartQuotientCover_finite :
    IsFinite (affineChartQuotientCover (R := R) (A := A) (G := G)).structureMap :=
  (affineChartQuotientCover (R := R) (A := A) (G := G)).finite_structureMap

theorem affineChartQuotientMap_structure :
    (affineChartQuotientMap (R := R) (A := A) (G := G)).left =
      Spec.map (CommRingCat.ofHom (Subalgebra.val (fixedPointSubalgebra R A G))) :=
  rfl

/-- The actual affine local quotient chart over the whole affine base. -/
noncomputable def affineChartLocalQuotientOfAlgebra :
    AffineChartLocalQuotient (Spec (CommRingCat.of R)) where
  U := ⊤
  hU := inferInstance
  XU := affineCover (R := R) A inferInstance inferInstance
  hXU := inferInstance
  Q := affineChartQuotientCover (R := R) (A := A) (G := G)

namespace affineChartLocalQuotientOfAlgebra

/-- The chart map of the affine local quotient is the chart quotient map. -/
theorem chartMap_eq :
    (affineChartLocalQuotientOfAlgebra (R := R) (A := A) (G := G)).chartMap =
      (affineChartQuotientCover (R := R) (A := A) (G := G)).structureMap ≫
        (⊤ : (Spec (CommRingCat.of R)).Opens).ι :=
  rfl

theorem chartMap_etale :
    Etale (affineChartLocalQuotientOfAlgebra (R := R) (A := A) (G := G)).chartMap :=
  (affineChartLocalQuotientOfAlgebra (R := R) (A := A) (G := G)).chartMap_etale

end affineChartLocalQuotientOfAlgebra

/-- Algebra-level local quotient consumer: actual chart and chart map. -/
theorem affineChartLocalQuotientConstruction_affine :
    ∃ D : AffineChartLocalQuotient (Spec (CommRingCat.of R)),
      D.U = ⊤ ∧ D.XU = affineCover (R := R) A inferInstance inferInstance :=
  ⟨affineChartLocalQuotientOfAlgebra (R := R) (A := A) (G := G), rfl, rfl⟩

end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartFamilyQuotient
end