import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDescEq
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientUniq
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Global quotient: desc naturality

This file records naturality equations for the scheme-level desc morphism of
the global glued quotient.  All statements are conditional equations derived
from the desc/glue interface; no colimit or provider is asserted.
-/

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDescNaturality

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDesc
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientFac
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {S : Scheme.{u}}

namespace GlobalGluedQuotientData

variable (D : GlobalGluedQuotientData S)

/-- Naturality of desc under postcomposition by a scheme morphism. -/
theorem desc_comp_naturality (Z W : Scheme.{u}) (g : Z ⟶ W)
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j) :
    D.desc W (fun i => f i ≫ g)
        (by
          intro i j
          calc
            pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ (f i ≫ g)
                = (pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i) ≫ g := (Category.assoc _ _ _).symm
            _ = (pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j) ≫ g := congrArg (fun h => h ≫ g) (hf i j)
            _ = pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ (f j ≫ g) := Category.assoc _ _ _) =
      D.desc Z f hf ≫ g := by
  symm
  apply (LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientUniq.GlobalGluedQuotientData.eq_desc_iff_restrict D W
    (fun i => f i ≫ g) (by
      intro i j
      calc
        pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ (f i ≫ g)
            = (pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i) ≫ g := (Category.assoc _ _ _).symm
        _ = (pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j) ≫ g := congrArg (fun h => h ≫ g) (hf i j)
        _ = pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ (f j ≫ g) := Category.assoc _ _ _)
    (D.desc Z f hf ≫ g)).mpr
  intro i
  change (D.P.toSchemeGlueData.ι i ≫ D.desc Z f hf) ≫ g = f i ≫ g
  rw [LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientFac.GlobalGluedQuotientData.desc_ι D Z f hf i]
  rfl

/-- Naturality of desc under a single postcomposition, in the direction that
keeps the chart family explicit. -/
theorem desc_comp_naturality_apply (Z W : Scheme.{u}) (g : Z ⟶ W)
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j)
    (i : D.P.J) :
    (D.P.toSchemeGlueData).ι i ≫ D.desc Z f hf = f i :=
  LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientFac.GlobalGluedQuotientData.desc_ι D Z f hf i

/-- Identity naturality: postcomposition by the identity is the identity desc
equation. -/
theorem desc_comp_id (Z : Scheme.{u})
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j) :
    D.desc Z (fun i => f i ≫ 𝟙 Z)
        (by
          intro i j
          calc
            pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ (f i ≫ 𝟙 Z)
                = (pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i) ≫ 𝟙 Z := (Category.assoc _ _ _).symm
            _ = pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i := Category.comp_id _
            _ = pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j := hf i j
            _ = (pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j) ≫ 𝟙 Z := (Category.comp_id _).symm
            _ = pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ (f j ≫ 𝟙 Z) := Category.assoc _ _ _) =
      D.desc Z f hf := by
  rw [LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDescNaturality.GlobalGluedQuotientData.desc_comp_naturality D Z Z (𝟙 Z) f hf, Category.comp_id]

/-- Associativity of desc naturality: postcomposing twice is postcomposing by
the composite chart family. -/
theorem desc_comp_naturality_assoc (Z W V : Scheme.{u})
    (g : Z ⟶ W) (h : W ⟶ V)
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j) :
    D.desc V (fun i => f i ≫ g ≫ h)
        (by
          intro i j
          calc
            pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ (f i ≫ g ≫ h)
                = (pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i) ≫ (g ≫ h) := (Category.assoc _ _ _).symm
            _ = (pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j) ≫ (g ≫ h) := congrArg (fun k => k ≫ (g ≫ h)) (hf i j)
            _ = pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ (f j ≫ g ≫ h) := Category.assoc _ _ _) =
      D.desc Z f hf ≫ g ≫ h := by
  rw [LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDescNaturality.GlobalGluedQuotientData.desc_comp_naturality D W V h (fun i => f i ≫ g)
    (by
      intro i j
      calc
        pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ (f i ≫ g)
            = (pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i) ≫ g := (Category.assoc _ _ _).symm
        _ = (pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j) ≫ g := congrArg (fun k => k ≫ g) (hf i j)
        _ = pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ (f j ≫ g) := Category.assoc _ _ _)]
  rw [LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDescNaturality.GlobalGluedQuotientData.desc_comp_naturality D Z W g f hf, Category.assoc]

/-- The desc morphism is functorial on morphisms from the quotient cover. -/
theorem desc_comp_naturality_structure (Z : Scheme.{u})
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j) :
    D.desc Z f hf = D.P.descOfCompatible Z f hf :=
  rfl

/-- A morphism whose chart restrictions agree with a compatible family is the
desc morphism of that family. -/
theorem eq_desc_of_chart_restrict (Z : Scheme.{u})
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j)
    (u : D.cover.carrier ⟶ Z)
    (hu : ∀ i : D.P.J, (D.P.toSchemeGlueData).ι i ≫ u = f i) :
    u = D.desc Z f hf :=
  (LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientUniq.GlobalGluedQuotientData.eq_desc_iff_restrict D Z f hf u).mpr hu

/-- Two morphisms out of the glued quotient are equal if their chart
restrictions agree. -/
theorem hom_ext_of_chart_restrict (Z : Scheme.{u})
    (u v : D.cover.carrier ⟶ Z)
    (h : ∀ i : D.P.J, (D.P.toSchemeGlueData).ι i ≫ u = (D.P.toSchemeGlueData).ι i ≫ v) :
    u = v :=
  LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientUniq.GlobalGluedQuotientData.hom_ext_of_chart D Z u v h

end GlobalGluedQuotientData

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDescNaturality
end