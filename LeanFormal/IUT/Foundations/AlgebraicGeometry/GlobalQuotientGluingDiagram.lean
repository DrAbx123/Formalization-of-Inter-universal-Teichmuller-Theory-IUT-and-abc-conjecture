import LeanFormal.IUT.Foundations.GlobalQuotientChartPresentationToGluedProof
import LeanFormal.IUT.Foundations.GlobalQuotientGluedCoverCocone
import Mathlib.CategoryTheory.Limits.IsColimit
import Mathlib.Tactic

/-!
# The actual gluing diagram for the affine chart family

This file constructs the gluing index category with chart objects and overlap
objects, its diagram to schemes, and the actual cocone whose point is the glued
finite etale cover carrier.  Cones over this diagram are exactly
overlap-compatible chart families, so the desc/fac/uniq universal property
gives the correct IsColimit target.  No diagram or colimit is postulated.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingDiagram

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartPresentation
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartPresentationToGluedProof
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluedCoverCocone
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalFiniteEtaleQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {S : Scheme.{u}} (D : GlobalQuotientChartPresentation S)

/-- The gluing index: charts and pairwise overlaps. -/
inductive GluingObject where
  | chart (i : D.J)
  | overlap (i j : D.J)

/-- Morphisms of the gluing index: identities, the two overlap inclusions, and
the overlap transition expressed through the second inclusion. -/
inductive GluingHom : GluingObject D → GluingObject D → Type u
  | id (X : GluingObject D) : GluingHom X X
  | fst (i j : D.J) : GluingHom (GluingObject.overlap i j) (GluingObject.chart i)
  | snd (i j : D.J) : GluingHom (GluingObject.overlap i j) (GluingObject.chart j)

namespace GluingHom

/-- Composition in the gluing index.  There are no composable non-identity
pairs except an overlap inclusion followed by an identity. -/
def comp : ∀ {X Y Z : GluingObject D},
    GluingHom D X Y → GluingHom D Y Z → GluingHom D X Z
  | _, _, _, .id _, g => g
  | _, _, _, f, .id _ => f

end GluingHom

/-- The gluing index category. -/
instance gluingCategory : Category (GluingObject D) where
  Hom := GluingHom D
  id := GluingHom.id
  comp := GluingHom.comp
  id_comp := by
    intro X Y f
    cases f
    rfl
  comp_id := by
    intro X Y f
    cases f
    rfl
  assoc := by
    intro W X Y Z f g h
    cases f <;> cases g <;> cases h <;> rfl

/-- The actual gluing diagram: charts and overlaps. -/
noncomputable def gluingDiagram : GluingObject D ⥤ Scheme.{u} where
  obj X :=
    match X with
    | GluingObject.chart i => D.U i
    | GluingObject.overlap i j => D.V i j
  map := by
    intro X Y f
    match f with
    | GluingHom.id X => exact 𝟙 _
    | GluingHom.fst i j => exact D.f i j
    | GluingHom.snd i j => exact D.f' i j
  map_id := by
    intro X
    cases X <;> rfl
  map_comp := by
    intro X Y Z f g
    cases f <;> cases g <;> rfl

/-- The overlap map used by the actual cocone. -/
noncomputable def overlapToCover (i j : D.J) :
    D.V i j ⟶ (toGluedData D).cover.carrier :=
  D.f i j ≫ chartToCover D i

/-- The actual cocone over the gluing diagram, with point the actual cover
carrier. -/
noncomputable def gluingCocone : Cocone (gluingDiagram D) where
  pt := (toGluedData D).cover.carrier
  ι :=
    { app := fun X =>
        match X with
        | GluingObject.chart i => chartToCover D i
        | GluingObject.overlap i j => overlapToCover D i j
      naturality := by
        intro X Y f
        cases f with
        | id X =>
            cases X <;> rfl
        | fst i j =>
            rfl
        | snd i j =>
            change D.f' i j ≫ chartToCover D j = D.f i j ≫ chartToCover D i
            rw [chartToCover_eq_chartι, chartToCover_eq_chartι]
            change (D.toSchemeGlueData).t i j ≫ (D.toSchemeGlueData).f j i ≫
              (D.toSchemeGlueData).ι j =
              (D.toSchemeGlueData).f i j ≫ (D.toSchemeGlueData).ι i
            exact (D.toSchemeGlueData).glue_condition i j }

/-- The chart component of the gluing cocone. -/
theorem gluingCocone_chart (i : D.J) :
    (gluingCocone D).ι.app (GluingObject.chart i) = chartToCover D i := rfl

/-- The overlap component of the gluing cocone. -/
theorem gluingCocone_overlap (i j : D.J) :
    (gluingCocone D).ι.app (GluingObject.overlap i j) = overlapToCover D i j := rfl

/-- A cone over the gluing diagram restricts to a compatible chart family. -/
noncomputable def coneFamily (c : Cocone (gluingDiagram D)) :
    ∀ i : D.J, D.U i ⟶ c.pt :=
  fun i => c.ι.app (GluingObject.chart i)

/-- The chart family of a cone is overlap-compatible. -/
theorem coneFamily_compat (c : Cocone (gluingDiagram D)) (i j : D.J) :
    pullback.fst ((D.toSchemeGlueData).ι i) ((D.toSchemeGlueData).ι j) ≫
        coneFamily D c i =
      pullback.snd ((D.toSchemeGlueData).ι i) ((D.toSchemeGlueData).ι j) ≫
        coneFamily D c j := by
  have hfst : (gluingDiagram D).map (GluingHom.fst i j) ≫
      c.ι.app (GluingObject.chart i) = c.ι.app (GluingObject.overlap i j) :=
    c.ι.naturality (GluingHom.fst i j)
  have hsnd : (gluingDiagram D).map (GluingHom.snd i j) ≫
      c.ι.app (GluingObject.chart j) = c.ι.app (GluingObject.overlap i j) :=
    c.ι.naturality (GluingHom.snd i j)
  rw [← hfst, ← hsnd]
  change D.f i j ≫ coneFamily D c i = D.f' i j ≫ coneFamily D c j
  rw [chartToCover_eq_chartι]
  change (D.toSchemeGlueData).f i j ≫ (D.toSchemeGlueData).ι i =
    (D.toSchemeGlueData).t i j ≫ (D.toSchemeGlueData).f j i ≫
      (D.toSchemeGlueData).ι j
  exact ((D.toSchemeGlueData).glue_condition i j).symm

/-- The actual desc morphism from a cone over the gluing diagram. -/
noncomputable def coneDesc (c : Cocone (gluingDiagram D)) :
    (gluingCocone D).pt ⟶ c.pt :=
  coconeDesc D c.pt (coneFamily D c) (by
    intro i j
    exact coneFamily_compat D c i j)

/-- The cone desc restricts to the chart components. -/
theorem coneDesc_fac (c : Cocone (gluingDiagram D)) (i : D.J) :
    (gluingCocone D).ι.app (GluingObject.chart i) ≫ coneDesc D c =
      c.ι.app (GluingObject.chart i) :=
  coconeDesc_fac D c.pt (coneFamily D c) (by
    intro i j
    exact coneFamily_compat D c i j) i

/-- The cone desc also restricts to the overlap components, using the cocone
naturality. -/
theorem coneDesc_fac_overlap (c : Cocone (gluingDiagram D)) (i j : D.J) :
    (gluingCocone D).ι.app (GluingObject.overlap i j) ≫ coneDesc D c =
      c.ι.app (GluingObject.overlap i j) := by
  rw [gluingCocone_overlap]
  change (D.f i j ≫ chartToCover D i) ≫ coneDesc D c = c.ι.app (GluingObject.overlap i j)
  rw [Category.assoc, coneDesc_fac]
  exact (c.ι.naturality (GluingHom.fst i j)).symm

/-- The universal property: every cone descends uniquely. -/
theorem coneDesc_exists_unique (c : Cocone (gluingDiagram D)) :
    ∃! u : (gluingCocone D).pt ⟶ c.pt,
      ∀ X : GluingObject D, (gluingCocone D).ι.app X ≫ u = c.ι.app X := by
  refine ⟨coneDesc D c, ?_, ?_⟩
  · intro X
    cases X with
    | chart i => exact coneDesc_fac D c i
    | overlap i j => exact coneDesc_fac_overlap D c i j
  · intro u hu
    apply coconeDesc_uniq D c.pt (coneFamily D c) (by
      intro i j
      exact coneFamily_compat D c i j)
    intro i
    exact hu (GluingObject.chart i)

/-- The actual gluing cocone is a colimit. -/
noncomputable def gluingCocone_isColimit : IsColimit (gluingCocone D) where
  desc := coneDesc D
  fac := by
    intro c X
    cases X with
    | chart i => exact coneDesc_fac D c i
    | overlap i j => exact coneDesc_fac_overlap D c i j
  uniq := by
    intro c u hu
    apply coconeDesc_uniq D c.pt (coneFamily D c) (by
      intro i j
      exact coneFamily_compat D c i j)
    intro i
    exact hu (GluingObject.chart i)


namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingDiagram

variable {S : Scheme.{u}} (D : GlobalQuotientChartPresentation S)

/-- The gluing diagram sends a chart object to the chart scheme. -/
theorem gluingDiagram_obj_chart (i : D.J) :
    (gluingDiagram D).obj (GluingObject.chart i) = D.U i := rfl

/-- The gluing diagram sends an overlap object to the overlap scheme. -/
theorem gluingDiagram_obj_overlap (i j : D.J) :
    (gluingDiagram D).obj (GluingObject.overlap i j) = D.V i j := rfl

/-- The gluing diagram sends the first overlap inclusion to f. -/
theorem gluingDiagram_map_fst (i j : D.J) :
    (gluingDiagram D).map (GluingHom.fst i j) = D.f i j := rfl

/-- The gluing diagram sends the second overlap inclusion to f'. -/
theorem gluingDiagram_map_snd (i j : D.J) :
    (gluingDiagram D).map (GluingHom.snd i j) = D.f' i j := rfl

/-- The gluing cocone point is the actual cover carrier. -/
theorem gluingCocone_pt :
    (gluingCocone D).pt = (toGluedData D).cover.carrier := rfl

/-- The actual colimit witness. -/
noncomputable def gluingCoconeIsColimit : IsColimit (gluingCocone D) :=
  gluingCocone_isColimit D

/-- The colimit desc function is the cone desc. -/
theorem gluingCoconeIsColimit_desc (c : Cocone (gluingDiagram D)) :
    (gluingCocone_isColimit D).desc c = coneDesc D c := rfl

/-- The colimit fac equation at chart components. -/
theorem gluingCoconeIsColimit_fac_chart (c : Cocone (gluingDiagram D)) (i : D.J) :
    (gluingCocone D).ι.app (GluingObject.chart i) ≫
        (gluingCocone_isColimit D).desc c = c.ι.app (GluingObject.chart i) :=
  coneDesc_fac D c i

/-- The colimit fac equation at overlap components. -/
theorem gluingCoconeIsColimit_fac_overlap (c : Cocone (gluingDiagram D)) (i j : D.J) :
    (gluingCocone D).ι.app (GluingObject.overlap i j) ≫
        (gluingCocone_isColimit D).desc c = c.ι.app (GluingObject.overlap i j) :=
  coneDesc_fac_overlap D c i j

/-- The gluing cocone is a colimit for every cone over the actual diagram. -/
theorem gluingCocone_desc_exists_unique (c : Cocone (gluingDiagram D)) :
    ∃! u : (gluingCocone D).pt ⟶ c.pt,
      ∀ X : GluingObject D, (gluingCocone D).ι.app X ≫ u = c.ι.app X :=
  coneDesc_exists_unique D c

/-- A cone is determined by its chart components. -/
theorem cone_ext (c d : Cocone (gluingDiagram D))
    (h : ∀ i : D.J,
      c.ι.app (GluingObject.chart i) = d.ι.app (GluingObject.chart i)) : c = d := by
  cases c with
  | mk cp ci =>
    cases d with
    | mk dp di =>
      simp only at h
      congr
      funext X
      cases X with
      | chart i => exact h i
      | overlap i j =>
          rw [← ci.naturality (GluingHom.fst i j), ← di.naturality (GluingHom.fst i j)]
          simp only [gluingDiagram_map_fst]
          rw [h i]

/-- The actual colimit witness is the gluing cocone. -/
theorem gluingCoconeIsColimit_cocone :
    (gluingCocone_isColimit D).cocone = gluingCocone D := rfl


namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingDiagram

variable {S : Scheme.{u}} (D : GlobalQuotientChartPresentation S)

/-- The gluing category has chart objects and overlap objects. -/
theorem gluingObject_cases (X : GluingObject D) :
    (∃ i : D.J, X = GluingObject.chart i) ∨
      (∃ i j : D.J, X = GluingObject.overlap i j) := by
  cases X with
  | chart i => exact Or.inl ⟨i, rfl⟩
  | overlap i j => exact Or.inr ⟨i, j, rfl⟩

/-- The actual gluing cocone is a colimit of the actual gluing diagram. -/
theorem gluingCocone_isColimit' : Nonempty (IsColimit (gluingCocone D)) :=
  ⟨gluingCocone_isColimit D⟩

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingDiagram

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingDiagram

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingDiagram
