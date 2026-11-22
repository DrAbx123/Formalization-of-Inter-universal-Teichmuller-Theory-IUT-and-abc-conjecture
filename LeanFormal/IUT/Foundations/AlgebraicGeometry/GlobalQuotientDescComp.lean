import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDescNaturality
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Global quotient: desc composition equations

Additional composition laws for the scheme-level desc morphism.  These are
post-compile-delta drafts: they are held for the next batch and are not part of
the running compile manifest.
-/

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDescComp

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDesc
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientFac
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDescNaturality
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {S : Scheme.{u}}

namespace GlobalGluedQuotientData

variable (D : GlobalGluedQuotientData S)

/-- Desc naturality for a composite of two postcompositions. -/
theorem desc_comp_comp (Z W V : Scheme.{u}) (g : Z ⟶ W) (h : W ⟶ V)
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j) :
    D.desc V (fun i => f i ≫ g ≫ h)
        (by
          intro i j
          simpa [Category.assoc] using congrArg (fun k => k ≫ g ≫ h) (hf i j)) =
      D.desc Z f hf ≫ g ≫ h :=
  D.desc_comp_naturality_assoc Z W V g h f hf

/-- Desc naturality under postcomposition by an isomorphism. -/
theorem desc_comp_iso (Z W : Scheme.{u}) (e : Z ≅ W)
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j) :
    D.desc W (fun i => f i ≫ e.hom)
        (by
          intro i j
          simpa [Category.assoc] using congrArg (fun k => k ≫ e.hom) (hf i j)) =
      D.desc Z f hf ≫ e.hom :=
  D.desc_comp_naturality Z W e.hom f hf

/-- Desc naturality for a chart family that is already postcomposed. -/
theorem desc_comp_apply_chart (Z W : Scheme.{u}) (g : Z ⟶ W)
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j)
    (i : D.P.J) :
    (D.P.toSchemeGlueData).ι i ≫ D.desc W (fun i => f i ≫ g)
        (by
          intro i j
          simpa [Category.assoc] using congrArg (fun k => k ≫ g) (hf i j)) =
      f i ≫ g :=
  D.desc_ι W (fun i => f i ≫ g)
    (by
      intro i j
      simpa [Category.assoc] using congrArg (fun k => k ≫ g) (hf i j)) i

end GlobalGluedQuotientData

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDescComp
end