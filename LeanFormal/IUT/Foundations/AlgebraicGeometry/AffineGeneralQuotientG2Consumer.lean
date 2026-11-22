import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleFixedPointsGeneral
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
import LeanFormal.IUT.Foundations.AlgebraicGeometry.InvariantsGeneralAssembly
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
import Mathlib.Tactic

/-!
# Affine general quotient/G2 consumer

This file instantiates the affine quotient construction and its lift/fac
consumer with the general finite-etale fixed-point theorem
FiniteEtaleFixedPointsGeneral.fixedPointSubalgebra_finiteEtale, removing the
local-base hypothesis used by the earlier local consumer.

Scope: conditional on a finite etale affine A/R and a finite G-action; this is
not a global provider for arbitrary schemes or a global quotient claim.
-/

open AlgebraicGeometry CategoryTheory
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer

universe u

variable {R : Type u} [CommRing R]

/-- General affine quotient cover: no local-base hypothesis. -/
noncomputable def affineQuotientCoverGeneral
    (A G : Type u) [CommRing A] [Algebra R A]
    [Group G] [Fintype G] [DecidableEq G]
    [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.Etale R A] [Module.Finite R A] :
    FiniteEtaleCover (baseSpec (R := R)) :=
  let h := FiniteEtaleFixedPointsGeneral.fixedPointSubalgebra_finiteEtale
    (R := R) (A := A) (G := G)
  FiniteEtaleCover.mk
    (Spec.map (CommRingCat.ofHom (algebraMap R (fixedPointSubalgebra R A G))))
    (specMap_etale_of_algebra_etale (R := R) h.1)
    (specMap_finite_of_module_finite (R := R) h.2)

/-- The canonical map from the affine cover to its general quotient cover. -/
noncomputable def affineQuotientCoverMapGeneral
    (A G : Type u) [CommRing A] [Algebra R A]
    [Group G] [Fintype G] [DecidableEq G]
    [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.Etale R A] [Module.Finite R A] :
    affineCover (R := R) A inferInstance inferInstance ⟶
      affineQuotientCoverGeneral (R := R) A G :=
  AffineLocalQuotientGluingConstruct.finiteEtaleCoverHomMk
    (X := affineCover (R := R) A inferInstance inferInstance)
    (Y := affineQuotientCoverGeneral (R := R) A G)
    (Spec.map (CommRingCat.ofHom (Subalgebra.val (fixedPointSubalgebra R A G))))
    (by
      change Spec.map (CommRingCat.ofHom (Subalgebra.val (fixedPointSubalgebra R A G))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (fixedPointSubalgebra R A G))) =
        Spec.map (CommRingCat.ofHom (algebraMap R A))
      rw [← Spec.map_comp]
      congr 1)

/-- General affine quotient lift: an invariant R-algebra map B -> A factors
through A^G, producing a morphism of finite etale covers. -/
theorem affineQuotientCover_liftGeneral
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Group G] [Fintype G] [DecidableEq G]
    [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.Etale R A] [Module.Finite R A]
    (hEtB : Algebra.Etale R B) (hFinB : Module.Finite R B)
    (φ : B →ₐ[R] A)
    (hφ : ∀ (g : G) (b : B), groupActionRingEquiv A G g (φ b) = φ b) :
    ∃ u : affineQuotientCoverGeneral (R := R) A G ⟶
        affineCover (R := R) B hEtB hFinB,
      affineQuotientCoverMapGeneral (R := R) A G ≫ u =
        affineCoverMapOfAlgHom (R := R) (A := A) (B := B)
          inferInstance inferInstance hEtB hFinB φ := by
  obtain ⟨ψ, hψ, -⟩ :=
    ABCBridge.InvariantsGeneralAssembly.affineFixedPointQuotient_universal
      R A G φ hφ
  let hFix := FiniteEtaleFixedPointsGeneral.fixedPointSubalgebra_finiteEtale
    (R := R) (A := A) (G := G)
  refine ⟨affineCoverMapOfAlgHom (R := R) (A := fixedPointSubalgebra R A G) (B := B)
    hFix.1 hFix.2 hEtB hFinB ψ, ?_⟩
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  unfold affineQuotientCoverMapGeneral affineCoverMapOfAlgHom
  change Spec.map (CommRingCat.ofHom (Subalgebra.val (fixedPointSubalgebra R A G))) ≫
      Spec.map (CommRingCat.ofHom (ψ : B →+* fixedPointSubalgebra R A G)) =
    Spec.map (CommRingCat.ofHom (φ : B →+* A))
  rw [← Spec.map_comp]
  congr 1
  rw [← CommRingCat.ofHom_comp]
  congr 1
  exact congrArg (fun f : B →ₐ[R] A => (f : B →+* A)) hψ

/-- The chosen general affine quotient lift. -/
noncomputable def affineQuotientCoverLiftGeneral
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Group G] [Fintype G] [DecidableEq G]
    [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.Etale R A] [Module.Finite R A]
    (hEtB : Algebra.Etale R B) (hFinB : Module.Finite R B)
    (φ : B →ₐ[R] A)
    (hφ : ∀ (g : G) (b : B), groupActionRingEquiv A G g (φ b) = φ b) :
    affineQuotientCoverGeneral (R := R) A G ⟶ affineCover (R := R) B hEtB hFinB :=
  Classical.choose
    (affineQuotientCover_liftGeneral (R := R) (A := A) (B := B) (G := G)
      hEtB hFinB φ hφ)

/-- Fac equation for the chosen general affine quotient lift. -/
theorem affineQuotientCoverLiftGeneral_fac
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Group G] [Fintype G] [DecidableEq G]
    [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.Etale R A] [Module.Finite R A]
    (hEtB : Algebra.Etale R B) (hFinB : Module.Finite R B)
    (φ : B →ₐ[R] A)
    (hφ : ∀ (g : G) (b : B), groupActionRingEquiv A G g (φ b) = φ b) :
    affineQuotientCoverMapGeneral (R := R) A G ≫
        affineQuotientCoverLiftGeneral (R := R) (A := A) (B := B) (G := G)
          hEtB hFinB φ hφ =
      affineCoverMapOfAlgHom (R := R) (A := A) (B := B)
        inferInstance inferInstance hEtB hFinB φ :=
  Classical.choose_spec
    (affineQuotientCover_liftGeneral (R := R) (A := A) (B := B) (G := G)
      hEtB hFinB φ hφ)

end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
