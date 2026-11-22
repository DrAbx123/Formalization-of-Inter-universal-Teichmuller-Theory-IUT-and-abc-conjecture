import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDesc

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Global glued quotient: factorization through the charts

This file proves the chart-restriction (factorization) law for the desc
morphism constructed in `GlobalQuotientDesc`.
-/

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientFac

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDesc
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {S : Scheme.{u}}

namespace GlobalGluedQuotientData

variable (D : GlobalGluedQuotientData S)

/-- Factorization of the desc morphism on each local quotient chart: the chart
inclusion followed by the desc morphism is the prescribed chart morphism. -/
theorem desc_ι (Z : Scheme.{u})
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j)
    (i : D.P.J) :
    (D.P.toSchemeGlueData).ι i ≫ D.desc Z f hf = f i :=
  D.P.descOfCompatible_ι Z f hf i

/-- The same factorization expressed directly with the production desc morphism. -/
theorem desc_restrict_chart (Z : Scheme.{u})
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j)
    (i : D.P.J) :
    (D.P.toSchemeGlueData).ι i ≫ D.P.descOfCompatible Z f hf = f i :=
  D.P.descOfCompatible_ι Z f hf i

/-- Factorization as an equality with the cover carrier morphism. -/
theorem desc_restrict_chart_cover (Z : Scheme.{u})
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j)
    (i : D.P.J) :
    (D.P.toSchemeGlueData).ι i ≫ D.desc Z f hf = f i :=
  D.P.descOfCompatible_ι Z f hf i

/-- Postcomposition naturality of the desc morphism. -/
theorem desc_postcomp (Z W : Scheme.{u}) (g : Z ⟶ W)
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j) :
    D.desc W (fun i => f i ≫ g)
        (by
          intro i j
          calc
            pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ (f i ≫ g)
                = (pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i) ≫ g := by
                  rw [← Category.assoc]
            _ = (pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j) ≫ g := by
                  rw [hf i j]
            _ = pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ (f j ≫ g) := by
                  rw [Category.assoc]) =
      D.desc Z f hf ≫ g := by
  symm
  change D.P.descOfCompatible Z f hf ≫ g =
    D.P.descOfCompatible W (fun i => f i ≫ g)
      (by
        intro i j
        calc
          pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ (f i ≫ g)
              = (pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i) ≫ g := by
                rw [← Category.assoc]
          _ = (pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j) ≫ g := by
                rw [hf i j]
          _ = pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ (f j ≫ g) := by
                rw [Category.assoc])
  apply D.P.descOfCompatible_unique (Z := W) (f := fun i => f i ≫ g)
  intro i
  rw [← Category.assoc, D.P.descOfCompatible_ι]
  rfl

/-- The desc construction is invariant under pointwise equal chart families. -/
theorem desc_congr (Z : Scheme.{u})
    (f f' : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j)
    (hf' : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f' i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f' j)
    (h : ∀ i : D.P.J, f i = f' i) :
    D.desc Z f hf = D.desc Z f' hf' := by
  change D.P.descOfCompatible Z f hf = D.P.descOfCompatible Z f' hf'
  apply D.P.descOfCompatible_unique (Z := Z) (f := f') (hf := hf')
    (u := D.P.descOfCompatible Z f hf)
  intro i
  rw [D.P.descOfCompatible_ι Z f hf i]
  exact h i

/-- The desc morphism composed with a chart inclusion is the chart map, in
associative form. -/
theorem desc_ι_assoc (Z : Scheme.{u})
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j)
    (i : D.P.J) :
    (D.P.toSchemeGlueData).ι i ≫ D.desc Z f hf = f i :=
  D.P.descOfCompatible_ι Z f hf i
end GlobalGluedQuotientData

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientFac
end