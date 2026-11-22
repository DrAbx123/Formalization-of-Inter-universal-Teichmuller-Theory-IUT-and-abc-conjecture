import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientFreeAction
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineFiniteEtaleQuotientConsumer

/-!
# Isomorphism of the regular quotient cover with Spec R

The fixed-point algebra of the regular permutation cover is R, via
regularPermutationSectionsEquiv.  Hence the regular quotient cover is isomorphic
to the identity finite etale cover Spec R, and the chart map composed with this
isomorphism is the structure map of the regular permutation cover.  No residual
data is introduced.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.RegularPermutationQuotientCoverIso

universe u

open ABCBridge.FiniteEtaleQuotientFreeAction
open ABCBridge.AffineFiniteEtaleQuotientConsumer
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable (R : Type u) [CommRing R]
variable (G : Type u) [Group G] [Fintype G]

/-- The fixed-point algebra of the regular permutation algebra is R. -/
noncomputable abbrev regularFixedEquiv : FixedPoints.subalgebra R (G → R) G ≃+* R :=
  (regularPermutationSectionsEquiv (R := R) (G := G)).toRingEquiv

/-- The scheme isomorphism Spec((G -> R)^G) ≅ Spec R. -/
noncomputable def specFixedIsoSpecR :
    Spec (CommRingCat.of (FixedPoints.subalgebra R (G → R) G)) ≅
      Spec (CommRingCat.of R) :=
  Scheme.Spec.mapIso (((regularFixedEquiv (R := R) (G := G)).toCommRingCatIso.op).symm)

/-- The identity finite etale cover Spec R. -/
noncomputable def identityCover : FiniteEtaleCover (Spec (CommRingCat.of R)) where
  obj := Over.mk (𝟙 (Spec (CommRingCat.of R)))
  property := by
    change IsFiniteEtaleHom (𝟙 (Spec (CommRingCat.of R)))
    exact ⟨inferInstance, inferInstance⟩

/-- The quotient cover is isomorphic to the identity cover Spec R. -/
noncomputable def regularQuotientCoverIsoIdentity :
    regularQuotientCover (R := R) (G := G) ≅ identityCover (R := R) :=
  ObjectProperty.isoMk _ (Over.isoMk (specFixedIsoSpecR R G) (by
    change Spec.map (CommRingCat.ofHom (regularFixedEquiv (R := R) (G := G)).symm.toRingHom) ≫
        𝟙 (Spec (CommRingCat.of R)) =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (FixedPoints.subalgebra R (G → R) G)))
    rw [Category.comp_id]
    congr 1))

/-- The carrier of the regular quotient cover is isomorphic to Spec R. -/
noncomputable def regularQuotientCarrierIsoSpecR :
    (regularQuotientCover (R := R) (G := G)).carrier ≅ Spec (CommRingCat.of R) :=
  (specFixedIsoSpecR R G)

/-- The chart map followed by the quotient isomorphism has the underlying map of
the structure morphism of the regular permutation cover. -/
theorem regularQuotientChartMap_comp_iso :
    (regularQuotientChartMap (R := R) (G := G)).hom.left ≫
        (regularQuotientCarrierIsoSpecR R G).hom =
      (regularPermutationCover (R := R) (G := G)).structureMap := by
  change Spec.map (CommRingCat.ofHom
        (Subalgebra.val (FixedPoints.subalgebra R (G → R) G))) ≫
      Spec.map (CommRingCat.ofHom (regularFixedEquiv (R := R) (G := G)).symm.toRingHom) =
    Spec.map (CommRingCat.ofHom (algebraMap R (G → R)))
  rw [← Spec.map_comp]
  congr 1

/-- The chart map corresponds to the structure map of the regular cover under the
quotient isomorphism. -/
theorem regularQuotientChartMap_corresponds_structureMap :
    Nonempty (regularQuotientCover (R := R) (G := G) ≅ identityCover (R := R)) ∧
      ((regularQuotientChartMap (R := R) (G := G)).hom.left ≫
        (regularQuotientCarrierIsoSpecR R G).hom =
          (regularPermutationCover (R := R) (G := G)).structureMap) :=
  ⟨⟨regularQuotientCoverIsoIdentity R G⟩, regularQuotientChartMap_comp_iso R G⟩

end LeanFormal.IUT.Foundations.AlgebraicGeometry.RegularPermutationQuotientCoverIso
