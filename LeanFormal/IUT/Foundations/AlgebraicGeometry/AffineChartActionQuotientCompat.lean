import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartFamilyAction
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartFamilyQuotient
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Affine chart action/quotient compatibility

This file pairs the induced action on an affine chart restriction with the
local affine quotient chart.  It proves that the chart quotient map is
invariant under the action and records the exact overlap compatibility target
for two affine charts.

Post-compile-delta draft; held for watchdog compilation. No provider/IsColimit.
-/

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartActionQuotientCompat

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartFamilyFromCover
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartFamilyQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R G A : Type u} [CommRing R] [Group G] [Fintype G] [DecidableEq G]
  [CommRing A] [Algebra R A] [MulSemiringAction G A] [SMulCommClass G R A]
  [Algebra.Etale R A] [Module.Finite R A]

/-- The actual action endomorphism of the affine cover associated to a group
element. -/
noncomputable def affineCoverActionEnd (g : G) :
    affineCover (R := R) A inferInstance inferInstance ⟶
      affineCover (R := R) A inferInstance inferInstance :=
  finiteEtaleCoverHomMk
    (X := affineCover (R := R) A inferInstance inferInstance)
    (Y := affineCover (R := R) A inferInstance inferInstance)
    (Spec.map (CommRingCat.ofHom (groupActionRingEquiv A G g)))
    (by
      change Spec.map (CommRingCat.ofHom (groupActionRingEquiv A G g : A →+* A)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R A)) =
        Spec.map (CommRingCat.ofHom (algebraMap R A))
      rw [← Spec.map_comp]
      congr 1
      rw [← CommRingCat.ofHom_comp]
      congr 1
      ext r
      change (MulSemiringAction.toRingEquiv G A g) (algebraMap R A r) = algebraMap R A r
      rw [MulSemiringAction.toRingEquiv_apply_apply, smul_algebraMap])

theorem affineCoverActionEnd_structure (g : G) :
    (affineCoverActionEnd (R := R) (A := A) (G := G) g).left.left =
      Spec.map (CommRingCat.ofHom (groupActionRingEquiv A G g : A →+* A)) :=
  rfl

/-- The affine chart quotient map is invariant under the cover action: the
action on the cover followed by the quotient chart map is the chart map. -/
theorem affineChartQuotientMap_invariant (g : G) :
    affineCoverActionEnd (R := R) (A := A) (G := G) g ≫
        affineChartQuotientMap (R := R) (A := A) (G := G) =
      affineChartQuotientMap (R := R) (A := A) (G := G) :=
  by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    change Spec.map (CommRingCat.ofHom (groupActionRingEquiv A G g : A →+* A)) ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.val (fixedPointSubalgebra R A G))) =
      Spec.map (CommRingCat.ofHom (Subalgebra.val (fixedPointSubalgebra R A G)))
    rw [← Spec.map_comp]
    congr 1
    rw [← CommRingCat.ofHom_comp]
    congr 1
    ext x
    change (MulSemiringAction.toRingEquiv G A g) (x : A) = (x : A)
    rw [MulSemiringAction.toRingEquiv_apply_apply]
    exact x.2 g

/-- The local quotient chart paired with the restricted action. -/
noncomputable def affineChartActionQuotientPair :
    AffineChartLocalQuotient (Spec (CommRingCat.of R)) :=
  affineChartLocalQuotientOfAlgebra (R := R) (A := A) (G := G)

theorem affineChartActionQuotientPair_U :
    (affineChartActionQuotientPair (R := R) (A := A) (G := G)).U = ⊤ :=
  rfl

theorem affineChartActionQuotientPair_XU :
    (affineChartActionQuotientPair (R := R) (A := A) (G := G)).XU =
      affineCover (R := R) A inferInstance inferInstance :=
  rfl

/-- Equivariance of the chart map: postcomposing the chart map by the quotient
chart action is trivial because the quotient chart map is invariant. -/
theorem affineChartActionQuotientPair_chartMap_invariant (g : G) :
    affineCoverActionEnd (R := R) (A := A) (G := G) g ≫
        (affineChartActionQuotientPair (R := R) (A := A) (G := G)).chartMap =
      (affineChartActionQuotientPair (R := R) (A := A) (G := G)).chartMap :=
  affineChartQuotientMap_invariant (R := R) (A := A) (G := G) g

theorem affineChartQuotientMap_structure :
    affineChartQuotientMap (R := R) (A := A) (G := G) ≫
        (affineChartQuotientCover (R := R) (A := A) (G := G)).structureMap =
      (affineCover (R := R) A inferInstance inferInstance).structureMap :=
  rfl

/-- Explicit overlap compatibility target for two affine chart quotient charts:
there is a common open refinement on which the chart maps to the base agree.
This is the exact remaining overlap condition; it is a Prop, not an inhabited
provider or a placeholder field. -/
def AffineChartQuotientOverlapCompatibility (S : Scheme.{u}) : Prop :=
  ∀ (D₁ D₂ : AffineChartLocalQuotient S),
    ∃ (W : Scheme.{u}) (f₁ : W ⟶ D₁.Q.carrier) (f₂ : W ⟶ D₂.Q.carrier),
      IsOpenImmersion f₁ ∧ IsOpenImmersion f₂ ∧
        f₁ ≫ D₁.chartMap = f₂ ≫ D₂.chartMap


theorem affineChartActionQuotientPair_chartMap_etale :
    Etale (affineChartActionQuotientPair (R := R) (A := A) (G := G)).chartMap :=
  (affineChartActionQuotientPair (R := R) (A := A) (G := G)).chartMap_etale

theorem affineChartActionQuotientPair_chartMap_structure :
    (affineChartActionQuotientPair (R := R) (A := A) (G := G)).chartMap =
      (affineChartQuotientCover (R := R) (A := A) (G := G)).structureMap ≫
        (⊤ : (Spec (CommRingCat.of R)).Opens).ι :=
  rfl

/-- Diagonal overlap compatibility: each local quotient chart is compatible
with itself on its own carrier. -/
theorem affineChartQuotientOverlapCompatibility_diagonal
    (D : AffineChartLocalQuotient S) :
    ∃ (W : Scheme.{u}) (f₁ f₂ : W ⟶ D.Q.carrier),
      IsOpenImmersion f₁ ∧ IsOpenImmersion f₂ ∧
        f₁ ≫ D.chartMap = f₂ ≫ D.chartMap :=
  ⟨D.Q.carrier, 𝟙 _, 𝟙 _, inferInstance, inferInstance, rfl⟩

end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartActionQuotientCompat
end
end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartActionQuotientCompat
end
end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartActionQuotientCompat
end