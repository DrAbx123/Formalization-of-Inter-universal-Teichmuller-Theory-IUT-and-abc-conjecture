import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2

open AlgebraicGeometry CategoryTheory

set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientLiftUniqueness

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R A B G : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]
  [Algebra.Etale R A] [Module.Finite R A] [IsLocalRing R]
  (hEtB : Algebra.Etale R B) (hFinB : Module.Finite R B)

/-- Canonical algebra lift of an invariant `R`-algebra map `B -> A` through `A^G`. -/
noncomputable def canonicalLiftAlgHom
    (φ : B →ₐ[R] A)
    (hφ : ∀ (g : G) (b : B), groupActionRingEquiv A G g (φ b) = φ b) :
    B →ₐ[R] fixedPointSubalgebra R A G :=
  Classical.choose (ABCBridge.InvariantsGeneralAssembly.affineFixedPointQuotient_universal
    R A G φ hφ)

theorem canonicalLiftAlgHom_comp_inclusion
    (φ : B →ₐ[R] A)
    (hφ : ∀ (g : G) (b : B), groupActionRingEquiv A G g (φ b) = φ b) :
    (fixedPointInclusion R A G).comp (canonicalLiftAlgHom (R := R) (A := A) (B := B) (G := G)
      φ hφ) = φ :=
  (Classical.choose_spec (ABCBridge.InvariantsGeneralAssembly.affineFixedPointQuotient_universal
    R A G φ hφ)).1

theorem canonicalLiftAlgHom_unique
    (φ : B →ₐ[R] A)
    (hφ : ∀ (g : G) (b : B), groupActionRingEquiv A G g (φ b) = φ b)
    (ψ : B →ₐ[R] fixedPointSubalgebra R A G)
    (hψ : (fixedPointInclusion R A G).comp ψ = φ) :
    ψ = canonicalLiftAlgHom (R := R) (A := A) (B := B) (G := G) φ hφ :=
  (Classical.choose_spec (ABCBridge.InvariantsGeneralAssembly.affineFixedPointQuotient_universal
    R A G φ hφ)).2 ψ hψ

/-- Canonical cover lift `Spec A^G -> Spec B` built from the canonical algebra lift. -/
noncomputable def canonicalCoverLift
    (φ : B →ₐ[R] A)
    (hφ : ∀ (g : G) (b : B), groupActionRingEquiv A G g (φ b) = φ b) :
    affineQuotientCover (R := R) A G ⟶ affineCover (R := R) B hEtB hFinB := by
  let hG := LeanFormal.IUT.Foundations.AlgebraicGeometry.ConstantRankFixedPoints.fixedPointSubalgebra_finiteEtale_of_local
    (R := R) (A := A) (G := G)
  exact affineCoverMapOfAlgHom (R := R) (A := fixedPointSubalgebra R A G) (B := B)
    hG.1 hG.2 hEtB hFinB (canonicalLiftAlgHom (R := R) (A := A) (B := B) (G := G) φ hφ)

theorem canonicalCoverLift_fac
    (φ : B →ₐ[R] A)
    (hφ : ∀ (g : G) (b : B), groupActionRingEquiv A G g (φ b) = φ b) :
    affineQuotientCoverMap (R := R) A G ≫
        canonicalCoverLift (R := R) (A := A) (B := B) (G := G) hEtB hFinB φ hφ =
      affineCoverMapOfAlgHom (R := R) (A := A) (B := B)
        inferInstance inferInstance hEtB hFinB φ := by
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  change Spec.map (CommRingCat.ofHom (Subalgebra.val (fixedPointSubalgebra R A G))) ≫
      Spec.map (CommRingCat.ofHom (canonicalLiftAlgHom (R := R) (A := A) (B := B) (G := G)
        φ hφ : B →+* fixedPointSubalgebra R A G)) =
    Spec.map (CommRingCat.ofHom (φ : B →+* A))
  rw [← Spec.map_comp]
  congr 1
  rw [← CommRingCat.ofHom_comp]
  congr 1
  exact congrArg (fun f : B →ₐ[R] A => (f : B →+* A))
    (canonicalLiftAlgHom_comp_inclusion (R := R) (A := A) (B := B) (G := G) φ hφ)

end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientLiftUniqueness
end