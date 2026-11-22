import LeanFormal.IUT.Foundations.AlgebraicGeometry.ConstantRankFixedPoints
import LeanFormal.IUT.Foundations.AlgebraicGeometry.InvariantsGeneralAssembly
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientGluedCover
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Tactic

open AlgebraicGeometry CategoryTheory

set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2

universe u

variable {R : Type u} [CommRing R]

open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

abbrev baseSpec : Scheme.{u} := Spec (CommRingCat.of R)

theorem specMap_etale_of_algebra_etale {A : Type u} [CommRing A] [Algebra R A]
    (h : Algebra.Etale R A) :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  exact RingHom.etale_algebraMap.mpr h

theorem specMap_finite_of_module_finite {A : Type u} [CommRing A] [Algebra R A]
    (h : Module.Finite R A) :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  rw [AlgebraicGeometry.IsFinite.SpecMap_iff]
  change (algebraMap R A).Finite
  rw [RingHom.finite_algebraMap]
  exact h

noncomputable def affineCover (A : Type u) [CommRing A] [Algebra R A]
    (hEt : Algebra.Etale R A) (hFin : Module.Finite R A) :
    FiniteEtaleCover (baseSpec (R := R)) :=
  FiniteEtaleCover.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (specMap_etale_of_algebra_etale (R := R) hEt)
    (specMap_finite_of_module_finite (R := R) hFin)

/-- Affine quotient cover `Spec A^G -> Spec R`, using production M3 over a local
base (the source-curve range). -/
noncomputable def affineQuotientCover (A G : Type u) [CommRing A] [Algebra R A]
    [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.Etale R A] [Module.Finite R A] [IsLocalRing R] :
    FiniteEtaleCover (baseSpec (R := R)) :=
  let h := LeanFormal.IUT.Foundations.AlgebraicGeometry.ConstantRankFixedPoints.fixedPointSubalgebra_finiteEtale_of_local
    (R := R) (A := A) (G := G)
  FiniteEtaleCover.mk
    (Spec.map (CommRingCat.ofHom (algebraMap R (fixedPointSubalgebra R A G))))
    (specMap_etale_of_algebra_etale (R := R) h.1)
    (specMap_finite_of_module_finite (R := R) h.2)

noncomputable def affineQuotientCoverMap (A G : Type u) [CommRing A] [Algebra R A]
    [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.Etale R A] [Module.Finite R A] [IsLocalRing R] :
    affineCover (R := R) A inferInstance inferInstance ⟶ affineQuotientCover (R := R) A G :=
  AffineLocalQuotientGluingConstruct.finiteEtaleCoverHomMk
    (X := affineCover (R := R) A inferInstance inferInstance)
    (Y := affineQuotientCover (R := R) A G)
    (Spec.map (CommRingCat.ofHom (Subalgebra.val (fixedPointSubalgebra R A G))))
    (by
      change Spec.map (CommRingCat.ofHom (Subalgebra.val (fixedPointSubalgebra R A G))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (fixedPointSubalgebra R A G))) =
        Spec.map (CommRingCat.ofHom (algebraMap R A))
      rw [← Spec.map_comp]
      congr 1)

/-- Cover morphism `Spec A -> Spec B` induced by an `R`-algebra map `B -> A`. -/
noncomputable def affineCoverMapOfAlgHom {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (hEtA : Algebra.Etale R A) (hFinA : Module.Finite R A)
    (hEtB : Algebra.Etale R B) (hFinB : Module.Finite R B)
    (φ : B →ₐ[R] A) :
    affineCover (R := R) A hEtA hFinA ⟶ affineCover (R := R) B hEtB hFinB :=
  AffineLocalQuotientGluingConstruct.finiteEtaleCoverHomMk
    (X := affineCover (R := R) A hEtA hFinA)
    (Y := affineCover (R := R) B hEtB hFinB)
    (Spec.map (CommRingCat.ofHom (φ : B →+* A)))
    (by
      change Spec.map (CommRingCat.ofHom (φ : B →+* A)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R B)) =
        Spec.map (CommRingCat.ofHom (algebraMap R A))
      rw [← Spec.map_comp]
      congr 1
      rw [← CommRingCat.ofHom_comp]
      congr 1
      ext b
      exact φ.commutes b)

/-- Affine quotient factorization for algebra maps: an invariant `R`-algebra map
`B -> A` factors through `A^G`, hence gives an actual morphism of finite etale
covers out of the affine quotient cover. -/
theorem affineQuotientCover_lift {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.Etale R A] [Module.Finite R A] [IsLocalRing R]
    (hEtB : Algebra.Etale R B) (hFinB : Module.Finite R B)
    (φ : B →ₐ[R] A)
    (hφ : ∀ (g : G) (b : B), groupActionRingEquiv A G g (φ b) = φ b) :
    ∃ u : affineQuotientCover (R := R) A G ⟶
        affineCover (R := R) B hEtB hFinB,
      affineQuotientCoverMap (R := R) A G ≫ u =
        affineCoverMapOfAlgHom (R := R) (A := A) (B := B)
          inferInstance inferInstance hEtB hFinB φ := by
  obtain ⟨ψ, hψ, -⟩ :=
    ABCBridge.InvariantsGeneralAssembly.affineFixedPointQuotient_universal
      R A G φ hφ
  refine ⟨affineCoverMapOfAlgHom (R := R) (A := fixedPointSubalgebra R A G) (B := B)
    (ConstantRankFixedPoints.fixedPointSubalgebra_finiteEtale_of_local (R := R) (A := A) (G := G)).1
    (ConstantRankFixedPoints.fixedPointSubalgebra_finiteEtale_of_local (R := R) (A := A) (G := G)).2
    hEtB hFinB ψ, ?_⟩
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  change Spec.map (CommRingCat.ofHom (Subalgebra.val (fixedPointSubalgebra R A G))) ≫
      Spec.map (CommRingCat.ofHom (ψ : B →+* fixedPointSubalgebra R A G)) =
    Spec.map (CommRingCat.ofHom (φ : B →+* A))
  rw [← Spec.map_comp]
  congr 1
  rw [← CommRingCat.ofHom_comp]
  congr 1
  exact congrArg (fun f : B →ₐ[R] A => (f : B →+* A)) hψ

/-- The chosen affine quotient factorization of an invariant algebra map. -/
noncomputable def affineQuotientCoverLift {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.Etale R A] [Module.Finite R A] [IsLocalRing R]
    (hEtB : Algebra.Etale R B) (hFinB : Module.Finite R B)
    (φ : B →ₐ[R] A)
    (hφ : ∀ (g : G) (b : B), groupActionRingEquiv A G g (φ b) = φ b) :
    affineQuotientCover (R := R) A G ⟶ affineCover (R := R) B hEtB hFinB :=
  Classical.choose (affineQuotientCover_lift (R := R) (A := A) (B := B) (G := G)
    hEtB hFinB φ hφ)

theorem affineQuotientCoverLift_fac {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.Etale R A] [Module.Finite R A] [IsLocalRing R]
    (hEtB : Algebra.Etale R B) (hFinB : Module.Finite R B)
    (φ : B →ₐ[R] A)
    (hφ : ∀ (g : G) (b : B), groupActionRingEquiv A G g (φ b) = φ b) :
    affineQuotientCoverMap (R := R) A G ≫
        affineQuotientCoverLift (R := R) (A := A) (B := B) (G := G)
          hEtB hFinB φ hφ =
      affineCoverMapOfAlgHom (R := R) (A := A) (B := B)
        inferInstance inferInstance hEtB hFinB φ :=
  Classical.choose_spec (affineQuotientCover_lift (R := R) (A := A) (B := B) (G := G)
    hEtB hFinB φ hφ)

end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
end
