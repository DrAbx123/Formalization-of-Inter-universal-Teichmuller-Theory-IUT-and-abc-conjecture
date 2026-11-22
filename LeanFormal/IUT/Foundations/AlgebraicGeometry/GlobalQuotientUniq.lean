import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientFac

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Global glued quotient: uniqueness and exact cocone/IsColimit residual

This file proves uniqueness of the desc morphism for the glued global quotient
and records the exact remaining global G2 cocone/IsColimit statement.
-/

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientUniq

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDesc
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientFac
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {S : Scheme.{u}}

namespace GlobalGluedQuotientData

variable (D : GlobalGluedQuotientData S)

/-- Uniqueness of the desc morphism: any morphism out of the glued quotient
whose chart restrictions are the prescribed compatible family equals the desc
construction. -/
theorem desc_unique (Z : Scheme.{u})
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j)
    (u : D.cover.carrier ⟶ Z)
    (hu : ∀ i : D.P.J, (D.P.toSchemeGlueData).ι i ≫ u = f i) :
    u = D.desc Z f hf :=
  D.P.descOfCompatible_unique Z f hf u hu

/-- The desc morphism is characterized by its chart restrictions. -/
theorem desc_eq_iff (Z : Scheme.{u})
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j)
    (u : D.cover.carrier ⟶ Z) :
    u = D.desc Z f hf ↔
      ∀ i : D.P.J, (D.P.toSchemeGlueData).ι i ≫ u = f i := by
  constructor
  · intro h i
    rw [h]
    change (D.P.toSchemeGlueData).ι i ≫ D.P.descOfCompatible Z f hf = f i
    rw [D.P.descOfCompatible_ι Z f hf i]
  · intro hu
    exact D.P.descOfCompatible_unique Z f hf u hu

/-- The desc construction is an actual section of the chart-restriction map on
compatible families. -/
theorem desc_restrict_self (Z : Scheme.{u})
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j)
    (i : D.P.J) :
    (D.P.toSchemeGlueData).ι i ≫ D.desc Z f hf = f i :=
  D.P.descOfCompatible_ι Z f hf i

/-- Morphisms out of the glued quotient are determined by their restrictions to
the local quotient charts. -/
theorem hom_ext_of_chart (Z : Scheme.{u})
    (u v : D.cover.carrier ⟶ Z)
    (h : ∀ i : D.P.J, (D.P.toSchemeGlueData).ι i ≫ u = (D.P.toSchemeGlueData).ι i ≫ v) :
    u = v := by
  apply D.P.toSchemeGlueData.openCover.hom_ext
  intro i
  exact h i

/-- A morphism is the desc morphism exactly when it has the prescribed chart
restrictions. -/
theorem eq_desc_iff_restrict (Z : Scheme.{u})
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j)
    (u : D.cover.carrier ⟶ Z) :
    u = D.desc Z f hf ↔
      ∀ i : D.P.J, (D.P.toSchemeGlueData).ι i ≫ u = f i := by
  constructor
  · intro h i
    rw [h]
    change (D.P.toSchemeGlueData).ι i ≫ D.P.descOfCompatible Z f hf = f i
    rw [D.P.descOfCompatible_ι Z f hf i]
  · intro h
    exact D.P.descOfCompatible_unique Z f hf u h

/-- Uniqueness in chart-restriction form for two desc morphisms with the same
chart family. -/
theorem desc_unique_chart (Z : Scheme.{u})
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j)
    (u : D.cover.carrier ⟶ Z)
    (hu : ∀ i : D.P.J, (D.P.toSchemeGlueData).ι i ≫ u = f i) :
    u = D.desc Z f hf :=
  D.P.descOfCompatible_unique Z f hf u hu
end GlobalGluedQuotientData

/-- Exact residual for the global G2 cocone/IsColimit: every finite-group action
diagram in `FiniteEtaleCover S` should have an actual colimit. This is a Prop
with no inhabitant and no provider claim; it is the only remaining global
condition after the glued universal property above. -/
def GlobalQuotientCoconeResidual (S : Scheme.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    HasColimitsOfShape (SingleObj G) (FiniteEtaleCover S)

/-- Per-diagram data for the missing cocone/IsColimit residual. -/
structure GlobalQuotientCoconeData {G : Type u} [Group G] [Finite G]
    {S : Scheme.{u}} (F : SingleObj G ⥤ FiniteEtaleCover S) where
  /-- The action-diagram cocone. -/
  cocone : Cocone F
  /-- Its actual colimit proof. -/
  isColimit : IsColimit cocone

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientUniq
end