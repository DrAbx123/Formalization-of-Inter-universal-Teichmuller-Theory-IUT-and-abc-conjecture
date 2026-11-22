import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartDescentConsumer
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Global quotient: chart naturality

Naturality of the affine chart descent morphisms under composition of algebra
maps. This is a post-compile-delta draft, held for the next batch; no provider
is built.
-/

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartNaturality

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartDescentConsumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R : Type u} [CommRing R]

/-- Chart descent factorization for a composite algebra map `φ ∘ ψ`: the chart
map followed by the chart desc morphism is the canonical cover morphism of the
composite. -/
theorem affineChartDesc_comp_fac
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    {G : Type u} [Group G] [Fintype G] [DecidableEq G]
    [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.Etale R A] [Module.Finite R A]
    (hEtC : Algebra.Etale R C) (hFinC : Module.Finite R C)
    (φ : B →ₐ[R] A)
    (hφ : ∀ (g : G) (b : B), groupActionRingEquiv A G g (φ b) = φ b)
    (ψ : C →ₐ[R] B) :
    affineChartMap (R := R) A G ≫
        affineChartDesc (R := R) (A := A) (B := C) (G := G) hEtC hFinC (φ.comp ψ)
          (by
            intro g c
            change groupActionRingEquiv A G g (φ (ψ c)) = φ (ψ c)
            exact hφ g (ψ c)) =
      affineCoverMapOfAlgHom (R := R) (A := A) (B := C)
        inferInstance inferInstance hEtC hFinC (φ.comp ψ) :=
  affineChartDesc_fac (R := R) (A := A) (B := C) (G := G) hEtC hFinC (φ.comp ψ)
    (by
      intro g c
      change groupActionRingEquiv A G g (φ (ψ c)) = φ (ψ c)
      exact hφ g (ψ c))

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartNaturality
end