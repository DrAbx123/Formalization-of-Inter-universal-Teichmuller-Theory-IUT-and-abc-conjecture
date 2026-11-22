import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleFixedPoints
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartCompat
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Chart action consumer for affine quotient covers

The group `G` acts on the affine chart `affineCover A`; the induced action on
the quotient fixed-point chart is trivial, and the canonical chart-to-quotient
map is `G`-equivariant.  This file records the actual chart action and the
equivariance square used by the global quotient gluing.
-/
namespace ABCBridge.GlobalQuotientChartActionConsumer

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleFixedPoints
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

universe u

variable {R : Type u} [CommRing R] {A G : Type u} [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G] [MulSemiringAction G A] [SMulCommClass G R A]
  [Algebra.Etale R A] [Module.Finite R A]

/-- The actual action endomorphism of the affine chart `Spec A → Spec R`
induced by an element of `G`.  It is the affine cover map associated with the
action algebra equivalence. -/
noncomputable def affineChartActionEnd (g : G) :
    affineCover (R := R) A inferInstance inferInstance ⟶
      affineCover (R := R) A inferInstance inferInstance :=
  affineCoverMapOfAlgHom (R := R) (A := A) (B := A)
    inferInstance inferInstance inferInstance inferInstance
    (MulSemiringAction.toAlgEquiv R A g)

/-- The action endomorphism is the identity on the quotient fixed-point chart.
The fixed-point inclusion lands in invariants, so the induced quotient map is
the canonical one. -/
theorem affineChartAction_quotient_eq (g : G) :
    affineChartActionEnd (R := R) (A := A) (G := G) g ≫
        affineQuotientCoverMapGeneral (R := R) (A := A) (G := G) =
      affineQuotientCoverMapGeneral (R := R) (A := A) (G := G) := by
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  unfold affineChartActionEnd affineCoverMapOfAlgHom affineQuotientCoverMapGeneral
  apply congrArg (Spec.map ∘ CommRingCat.ofHom)
  ext x
  exact (Subalgebra.mem_fixedPointSubalgebra.mp x.property g).symm

/-- The identity element acts by the identity chart endomorphism. -/
theorem affineChartActionEnd_one :
    affineChartActionEnd (R := R) (A := A) (G := G) (1 : G) = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  unfold affineChartActionEnd affineCoverMapOfAlgHom
  apply congrArg (Spec.map ∘ CommRingCat.ofHom)
  ext x
  rfl

/-- The action endomorphisms compose according to multiplication in `G`. -/
theorem affineChartActionEnd_mul (g h : G) :
    affineChartActionEnd (R := R) (A := A) (G := G) (g * h) =
      affineChartActionEnd (R := R) (A := A) (G := G) g ≫
        affineChartActionEnd (R := R) (A := A) (G := G) h := by
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  unfold affineChartActionEnd affineCoverMapOfAlgHom
  apply congrArg (Spec.map ∘ CommRingCat.ofHom)
  ext x
  exact MulSemiringAction.toAlgEquiv_apply R A (g * h) x

/-- The quotient fixed-point chart has trivial `G`-action. -/
theorem affineQuotientChartAction_end (g : G) :
    affineChartActionEnd (R := R) (A := A) (G := G) g ≫
        affineQuotientCoverMapGeneral (R := R) (A := A) (G := G) =
      affineQuotientCoverMapGeneral (R := R) (A := A) (G := G) :=
  affineChartAction_quotient_eq (R := R) (A := A) (G := G) g


section QuotientChartAction

/-- The action of `G` on the actual affine quotient cover.  The quotient
fixed-point chart is invariant, so this is the identity isomorphism; it is
still the actual action inherited from the chart action. -/
noncomputable def affineQuotientChartAction (g : G) :
    affineQuotientCoverGeneral (R := R) (A := A) (G := G) ≅
      affineQuotientCoverGeneral (R := R) (A := A) (G := G) :=
  Iso.refl _

theorem affineQuotientChartAction_hom (g : G) :
    (affineQuotientChartAction (R := R) (A := A) (G := G) g).hom = 𝟙 _ :=
  rfl

theorem affineQuotientChartAction_inv (g : G) :
    (affineQuotientChartAction (R := R) (A := A) (G := G) g).inv = 𝟙 _ :=
  rfl

theorem affineQuotientChartAction_one :
    affineQuotientChartAction (R := R) (A := A) (G := G) (1 : G) =
      Iso.refl (affineQuotientCoverGeneral (R := R) (A := A) (G := G)) :=
  rfl

theorem affineQuotientChartAction_mul (g h : G) :
    affineQuotientChartAction (R := R) (A := A) (G := G) (g * h) =
      affineQuotientChartAction (R := R) (A := A) (G := G) g ≪≫
        affineQuotientChartAction (R := R) (A := A) (G := G) h :=
  rfl

theorem affineQuotientChartAction_trans (g : G) :
    (affineQuotientChartAction (R := R) (A := A) (G := G) g).hom ≫
        (affineQuotientChartAction (R := R) (A := A) (G := G) g).inv = 𝟙 _ :=
  (affineQuotientChartAction (R := R) (A := A) (G := G) g).hom_inv_id

theorem affineQuotientChartAction_inv_hom (g : G) :
    (affineQuotientChartAction (R := R) (A := A) (G := G) g).inv ≫
        (affineQuotientChartAction (R := R) (A := A) (G := G) g).hom = 𝟙 _ :=
  (affineQuotientChartAction (R := R) (A := A) (G := G) g).inv_hom_id

theorem affineQuotientChartAction_comp_eq (g : G) :
    (affineQuotientChartAction (R := R) (A := A) (G := G) g).hom ≫
        (affineQuotientChartAction (R := R) (A := A) (G := G) g).inv =
      (affineQuotientChartAction (R := R) (A := A) (G := G) g).inv ≫
        (affineQuotientChartAction (R := R) (A := A) (G := G) g).hom :=
  by simp

end QuotientChartAction

section ChartActionNormalization

/-- The quotient action is definitionally the identity iso. -/
theorem affineQuotientChartAction_refl (g : G) :
    affineQuotientChartAction (R := R) (A := A) (G := G) g =
      Iso.refl (affineQuotientCoverGeneral (R := R) (A := A) (G := G)) :=
  rfl

/-- The chart action composed with the quotient map is independent of `g`. -/
theorem affineChartAction_quotient_eq_comp (g h : G) :
    affineChartActionEnd (R := R) (A := A) (G := G) g ≫
        affineQuotientCoverMapGeneral (R := R) (A := A) (G := G) =
      affineChartActionEnd (R := R) (A := A) (G := G) h ≫
        affineQuotientCoverMapGeneral (R := R) (A := A) (G := G) := by
  rw [affineChartAction_quotient_eq, affineChartAction_quotient_eq]

end ChartActionNormalization

section ActionNormalization

theorem affineChartActionEnd_congr {g h : G} (hgh : g = h) :
    affineChartActionEnd (R := R) (A := A) (G := G) g =
      affineChartActionEnd (R := R) (A := A) (G := G) h :=
  congrArg _ hgh

theorem affineQuotientChartAction_congr {g h : G} (hgh : g = h) :
    affineQuotientChartAction (R := R) (A := A) (G := G) g =
      affineQuotientChartAction (R := R) (A := A) (G := G) h :=
  congrArg _ hgh

end ActionNormalization

end ABCBridge.GlobalQuotientChartActionConsumer