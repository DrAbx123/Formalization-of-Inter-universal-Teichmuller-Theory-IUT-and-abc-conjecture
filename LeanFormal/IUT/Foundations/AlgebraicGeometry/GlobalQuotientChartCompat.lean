import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorFixedPointsBaseChange
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientGluedCover
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Affine quotient charts under flat base change

This file supplies the chart-level compatibility needed for the global
quotient gluing: the affine quotient cover of `A` base-changed along a flat
map `R → R'` is canonically the affine quotient cover of `R' ⊗[R] A`, and the
canonical affine cover maps are compatible with these identifications.

The comparison algebra equivalence is the production M1 theorem
`M1Final.tensorFixedPointsAlgEquiv`.
-/
namespace ABCBridge.GlobalQuotientChartCompat

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

universe u

variable {R : Type u} [CommRing R] {A G : Type u} [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G] [MulSemiringAction G A] [SMulCommClass G R A]
  [Algebra.Etale R A] [Module.Finite R A]
  {R' : Type u} [CommRing R'] [Algebra R R'] [Module.Flat R R']

/-- The general fixed-point algebra is finite etale over the base. -/
theorem affineQuotientFixedPoint_finiteEtale :
    Algebra.Etale R (fixedPointSubalgebra R A G) ∧
      Module.Finite R (fixedPointSubalgebra R A G) :=
  FiniteEtaleFixedPointsGeneral.fixedPointSubalgebra_finiteEtale
    (R := R) (A := A) (G := G)

/-- M1: fixed points commute with the flat base change `R → R'`. -/
noncomputable def affineQuotientBaseChangeAlgEquiv :
    TensorProduct R R' (fixedPointSubalgebra R A G) ≃ₐ[R']
      fixedPointSubalgebra R' (TensorProduct R R' A) G :=
  M1Final.tensorFixedPointsAlgEquiv (R := R) (A := A) (G := G) (T := R')

/-- The base-changed affine quotient cover as an actual finite etale cover of
`Spec R'`. -/
noncomputable def affineQuotientBaseChangeCover :
    FiniteEtaleCover (baseSpec (R := R')) :=
  letI : Algebra.Etale R (fixedPointSubalgebra R A G) :=
    (affineQuotientFixedPoint_finiteEtale (R := R) (A := A) (G := G)).1
  letI : Module.Finite R (fixedPointSubalgebra R A G) :=
    (affineQuotientFixedPoint_finiteEtale (R := R) (A := A) (G := G)).2
  FiniteEtaleCover.mk
    (Spec.map (CommRingCat.ofHom
      (algebraMap R' (TensorProduct R R' (fixedPointSubalgebra R A G)))))
    (specMap_etale_of_algebra_etale (R := R')
      (Algebra.Etale.baseChange R (fixedPointSubalgebra R A G) R'))
    (specMap_finite_of_module_finite (R := R')
      (Module.Finite.base_change R R' (fixedPointSubalgebra R A G)))

/-- The actual affine quotient cover of the base-changed algebra `R' ⊗ A`. -/
noncomputable def affineQuotientBaseChangeActualCover :
    FiniteEtaleCover (baseSpec (R := R')) :=
  affineQuotientCoverGeneral (R := R')
    (A := TensorProduct R R' A) (G := G)

/-- The comparison morphism from the base-changed quotient chart to the
actual quotient chart of `R' ⊗ A`, induced by M1. -/
noncomputable def affineQuotientBaseChangeCoverHom :
    affineQuotientBaseChangeCover (R := R) (A := A) (G := G) (R' := R') ⟶
      affineQuotientBaseChangeActualCover (R := R) (A := A) (G := G) (R' := R') :=
  AffineLocalQuotientGluingConstruct.finiteEtaleCoverHomMk
    (X := affineQuotientBaseChangeCover (R := R) (A := A) (G := G) (R' := R'))
    (Y := affineQuotientBaseChangeActualCover (R := R) (A := A) (G := G) (R' := R'))
    (Spec.map (CommRingCat.ofHom
      (affineQuotientBaseChangeAlgEquiv (R := R) (A := A) (G := G)
        (R' := R')).symm.toRingHom))
    (by
      change Spec.map (CommRingCat.ofHom
          (affineQuotientBaseChangeAlgEquiv (R := R) (A := A) (G := G)
            (R' := R')).symm.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R'
            (fixedPointSubalgebra R' (TensorProduct R R' A) G))) =
        Spec.map (CommRingCat.ofHom (algebraMap R'
          (TensorProduct R R' (fixedPointSubalgebra R A G))))
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact (affineQuotientBaseChangeAlgEquiv (R := R) (A := A) (G := G)
        (R' := R')).symm.commutes x)

/-- Inverse comparison morphism. -/
noncomputable def affineQuotientBaseChangeCoverInv :
    affineQuotientBaseChangeActualCover (R := R) (A := A) (G := G) (R' := R') ⟶
      affineQuotientBaseChangeCover (R := R) (A := A) (G := G) (R' := R') :=
  AffineLocalQuotientGluingConstruct.finiteEtaleCoverHomMk
    (X := affineQuotientBaseChangeActualCover (R := R) (A := A) (G := G) (R' := R'))
    (Y := affineQuotientBaseChangeCover (R := R) (A := A) (G := G) (R' := R'))
    (Spec.map (CommRingCat.ofHom
      (affineQuotientBaseChangeAlgEquiv (R := R) (A := A) (G := G)
        (R' := R')).toRingHom))
    (by
      change Spec.map (CommRingCat.ofHom
          (affineQuotientBaseChangeAlgEquiv (R := R) (A := A) (G := G)
            (R' := R')).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R'
            (TensorProduct R R' (fixedPointSubalgebra R A G)))) =
        Spec.map (CommRingCat.ofHom (algebraMap R'
          (fixedPointSubalgebra R' (TensorProduct R R' A) G)))
      rw [← Spec.map_comp]
      congr 1)

/-- The comparison is an isomorphism of finite etale covers. -/
noncomputable def affineQuotientBaseChangeCoverEquiv :
    affineQuotientBaseChangeCover (R := R) (A := A) (G := G) (R' := R') ≅
      affineQuotientBaseChangeActualCover (R := R) (A := A) (G := G) (R' := R') where
  hom := affineQuotientBaseChangeCoverHom (R := R) (A := A) (G := G) (R' := R')
  inv := affineQuotientBaseChangeCoverInv (R := R) (A := A) (G := G) (R' := R')
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    show (Spec.map (CommRingCat.ofHom
        (affineQuotientBaseChangeAlgEquiv (R := R) (A := A) (G := G)
          (R' := R')).symm.toRingHom) :
        (affineQuotientBaseChangeCover (R := R) (A := A) (G := G) (R' := R')).carrier ⟶
          (affineQuotientBaseChangeActualCover (R := R) (A := A) (G := G) (R' := R')).carrier) ≫
        (Spec.map (CommRingCat.ofHom
          (affineQuotientBaseChangeAlgEquiv (R := R) (A := A) (G := G)
            (R' := R')).toRingHom) :
          (affineQuotientBaseChangeActualCover (R := R) (A := A) (G := G) (R' := R')).carrier ⟶
            (affineQuotientBaseChangeCover (R := R) (A := A) (G := G) (R' := R')).carrier) =
      𝟙 (affineQuotientBaseChangeCover (R := R) (A := A) (G := G) (R' := R')).carrier
    rw [← Spec.map_comp]
    conv_rhs => rw [← Spec.map_id]
    apply Spec.map_injective
    apply CommRingCat.hom_ext
    intro x
    simp
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    show (Spec.map (CommRingCat.ofHom
        (affineQuotientBaseChangeAlgEquiv (R := R) (A := A) (G := G)
          (R' := R')).toRingHom) :
        (affineQuotientBaseChangeActualCover (R := R) (A := A) (G := G) (R' := R')).carrier ⟶
          (affineQuotientBaseChangeCover (R := R) (A := A) (G := G) (R' := R')).carrier) ≫
        (Spec.map (CommRingCat.ofHom
          (affineQuotientBaseChangeAlgEquiv (R := R) (A := A) (G := G)
            (R' := R')).symm.toRingHom) :
          (affineQuotientBaseChangeCover (R := R) (A := A) (G := G) (R' := R')).carrier ⟶
            (affineQuotientBaseChangeActualCover (R := R) (A := A) (G := G) (R' := R')).carrier) =
      𝟙 (affineQuotientBaseChangeActualCover (R := R) (A := A) (G := G) (R' := R')).carrier
    rw [← Spec.map_comp]
    conv_rhs => rw [← Spec.map_id]
    apply Spec.map_injective
    apply CommRingCat.hom_ext
    intro x
    simp

end ABCBridge.GlobalQuotientChartCompat