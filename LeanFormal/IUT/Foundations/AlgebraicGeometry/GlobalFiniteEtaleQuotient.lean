import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientGluedCover
import Mathlib.Tactic

/-!
# Global finite-etale quotient/G2 for affine base

Given a finite etale cover X over Spec R and an affine-chart quotient
presentation, this file constructs the candidate quotient finite etale cover by
gluing the affine quotient charts.  The universal property is stated as an
explicit residual proposition; no global provider or IsColimit claim is made
before that proposition is proved.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalFiniteEtaleQuotient

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R : Type u} [CommRing R]

/-- Gluing data for affine quotient charts, together with the finite map check. -/
structure AffineChartQuotientPresentation (S : Scheme.{u}) where
  P : AffineLocalQuotientPreglueData S
  hq : ∀ i j, pullback.fst ((P.toSchemeGlueData).ι i)
      ((P.toSchemeGlueData).ι j) ≫ P.q i =
      pullback.snd ((P.toSchemeGlueData).ι i) ((P.toSchemeGlueData).ι j) ≫ P.q j
  hfin : IsFinite (P.gluedMapOfCompatible hq)

/-- Candidate global quotient finite etale cover obtained by gluing affine
quotient charts. -/
noncomputable def AffineChartQuotientPresentation.quotientCover
    {S : Scheme.{u}} (D : AffineChartQuotientPresentation S) :
    FiniteEtaleCover S :=
  D.P.toFiniteEtaleCoverOfIsFinite D.hq D.hfin

/-- Input presentation for a global quotient of a finite etale cover X with a
finite G-action by cover automorphisms. -/
structure GlobalFiniteEtaleQuotientInput
    (X : FiniteEtaleCover (Spec (CommRingCat.of R))) (G : Type u) [Group G] where
  presentation : AffineChartQuotientPresentation (Spec (CommRingCat.of R))
  chartIso : X.carrier ≅ presentation.P.toSchemeGlueData.glued
  overTriangle : chartIso.hom ≫ FiniteEtaleCover.structureMap presentation.quotientCover =
    FiniteEtaleCover.structureMap X
  action : G →* CategoryTheory.Aut X

variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))}
  {G : Type u} [Group G] (D : GlobalFiniteEtaleQuotientInput X G)

/-- The candidate global quotient cover. -/
noncomputable def GlobalFiniteEtaleQuotientInput.quotientCover :
    FiniteEtaleCover (Spec (CommRingCat.of R)) :=
  D.presentation.quotientCover

/-- The projection from X to the candidate quotient, as a cover morphism. -/
noncomputable def GlobalFiniteEtaleQuotientInput.projection :
    X ⟶ D.quotientCover :=
  AffineLocalQuotientGluingConstruct.finiteEtaleCoverHomMk
    (X := X) (Y := D.quotientCover)
    D.chartIso.hom
    D.overTriangle

/-- Exact residual universal property for the candidate quotient. -/
def GlobalFiniteEtaleQuotientInput.universalPropertyResidual : Prop :=
  ∀ (Z : FiniteEtaleCover (Spec (CommRingCat.of R))) (f : X ⟶ Z),
    (∀ g : G, (D.action g).hom ≫ f = f) →
      ∃! u : D.quotientCover ⟶ Z, D.projection ≫ u = f


/-- Data for a global quotient obtained by gluing affine quotient charts. -/
structure GlobalGluedQuotientData (S : Scheme.{u}) where
  P : AffineLocalQuotientPreglueData S
  hq : ∀ i j, pullback.fst ((P.toSchemeGlueData).ι i)
      ((P.toSchemeGlueData).ι j) ≫ P.q i =
      pullback.snd ((P.toSchemeGlueData).ι i) ((P.toSchemeGlueData).ι j) ≫ P.q j
  hfin : IsFinite (P.gluedMapOfCompatible hq)

/-- The finite etale cover represented by the glued quotient data. -/
noncomputable def GlobalGluedQuotientData.cover
    {S : Scheme.{u}} (D : GlobalGluedQuotientData S) : FiniteEtaleCover S :=
  D.P.toFiniteEtaleCoverOfIsFinite D.hq D.hfin

/-- Scheme-level descent morphism out of the glued quotient, from compatible
maps on the affine quotient charts. -/
noncomputable def GlobalGluedQuotientData.desc
    {S : Scheme.{u}} (D : GlobalGluedQuotientData S) (Z : Scheme.{u})
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
      pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j) :
    D.P.toSchemeGlueData.glued ⟶ Z :=
  D.P.descOfCompatible Z f hf

/-- Fac equation for the glued descent morphism. -/
theorem GlobalGluedQuotientData.desc_fac
    {S : Scheme.{u}} (D : GlobalGluedQuotientData S) (Z : Scheme.{u})
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
      pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j)
    (i : D.P.J) :
    (D.P.toSchemeGlueData).ι i ≫ D.desc Z f hf = f i :=
  D.P.descOfCompatible_ι Z f hf i

/-- Uniqueness of the glued descent morphism. -/
theorem GlobalGluedQuotientData.desc_uniq
    {S : Scheme.{u}} (D : GlobalGluedQuotientData S) (Z : Scheme.{u})
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
      pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j)
    (u : D.P.toSchemeGlueData.glued ⟶ Z)
    (hu : ∀ i : D.P.J, (D.P.toSchemeGlueData).ι i ≫ u = f i) :
    u = D.desc Z f hf :=
  D.P.descOfCompatible_unique Z f hf u hu

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalFiniteEtaleQuotient
