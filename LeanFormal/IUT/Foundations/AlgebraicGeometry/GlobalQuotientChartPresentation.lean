import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalFiniteEtaleQuotient
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientGluedCover
import Mathlib.Tactic

/-!
# Affine chart presentations for the global quotient candidate

This file records the affine-chart data used by the global quotient assembly.
It is a presentation layer only: the actual glued quotient cover is built from
the pregluing data, and no provider or IsColimit claim is made here.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartPresentation

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalFiniteEtaleQuotient
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R : Type u} [CommRing R]

/-- Affine chart presentation for the global quotient: pregluing data, the
quotient-chart map to the base, its etaleness, and the finite check for the
glued map. -/
structure GlobalQuotientChartPresentation (S : Scheme.{u}) where
  P : AffineLocalQuotientPreglueData S
  hq : ∀ i j, pullback.fst ((P.toSchemeGlueData).ι i)
      ((P.toSchemeGlueData).ι j) ≫ P.q i =
      pullback.snd ((P.toSchemeGlueData).ι i) ((P.toSchemeGlueData).ι j) ≫ P.q j
  hfin : IsFinite (P.gluedMapOfCompatible hq)
  chartAffine : ∀ i, IsAffine (P.U i)
  chartEtale : ∀ i, Etale (P.q i)
  chartBase : ∀ i, P.q i = P.q i

namespace GlobalQuotientChartPresentation

variable {S : Scheme.{u}} (D : GlobalQuotientChartPresentation S)

/-- The affine chart index type. -/
abbrev J : Type u := D.P.J

/-- The affine quotient chart at i. -/
abbrev U (i : D.J) : Scheme.{u} := D.P.U i

/-- The overlap chart at (i,j). -/
abbrev V (i j : D.J) : Scheme.{u} := D.P.V (i, j)

/-- The overlap inclusion into the first chart. -/
abbrev f (i j : D.J) : D.V i j ⟶ D.U i := D.P.f i j

/-- The overlap inclusion into the second chart. -/
abbrev f' (i j : D.J) : D.V i j ⟶ D.U j := D.P.t i j ≫ D.P.f j i

/-- The transition isomorphism between overlaps. -/
abbrev t (i j : D.J) : D.V i j ⟶ D.V j i := D.P.t i j

/-- The quotient-chart map to the base. -/
abbrev q (i : D.J) : D.U i ⟶ S := D.P.q i

/-- The underlying scheme glue data. -/
abbrev toSchemeGlueData : Scheme.GlueData.{u} := D.P.toSchemeGlueData

/-- The glued quotient scheme. -/
abbrev glued : Scheme.{u} := D.P.toSchemeGlueData.glued

/-- The glued map to the base. -/
abbrev gluedMap : D.glued ⟶ S := D.P.gluedMapOfCompatible D.hq

/-- The open immersion of chart i into the glued scheme. -/
abbrev chartι (i : D.J) : D.U i ⟶ D.glued := (D.toSchemeGlueData).ι i

/-- The quotient finite etale cover carried by the chart presentation. -/
noncomputable def cover : FiniteEtaleCover S :=
  D.P.toFiniteEtaleCoverOfIsFinite D.hq D.hfin

/-- The structure map of the quotient cover is the glued map. -/
theorem cover_structureMap : FiniteEtaleCover.structureMap D.cover = D.gluedMap := rfl

/-- The carrier of the quotient cover is the glued scheme. -/
theorem cover_carrier : D.cover.carrier = D.glued := rfl

/-- The chart map into the quotient cover. -/
noncomputable def chartMap (i : D.J) : D.U i ⟶ D.cover.carrier :=
  D.chartι i

/-- The chart map lies over the base. -/
theorem chartMap_structureMap (i : D.J) :
    D.chartMap i ≫ FiniteEtaleCover.structureMap D.cover = D.q i := by
  change (D.toSchemeGlueData).ι i ≫ D.gluedMap = D.q i
  exact D.P.gluedMapOfCompatible_ι D.hq i

/-- The glued map is etale. -/
theorem gluedMap_etale : Etale D.gluedMap :=
  D.P.gluedMapOfCompatible_etale D.hq

/-- The glued quotient cover is finite etale over the base. -/
theorem cover_isFiniteEtale :
    Etale (FiniteEtaleCover.structureMap D.cover) ∧
      IsFinite (FiniteEtaleCover.structureMap D.cover) :=
  ⟨D.gluedMap_etale, D.hfin⟩

/-- The chart presentation has an affine quotient chart at every index. -/
theorem chart_isAffine (i : D.J) : IsAffine (D.U i) :=
  D.chartAffine i

/-- Every quotient chart map is etale. -/
theorem chart_q_etale (i : D.J) : Etale (D.q i) :=
  D.chartEtale i

/-- The overlap inclusion is an open immersion. -/
theorem f_open (i j : D.J) : IsOpenImmersion (D.f i j) :=
  D.P.f_open i j

/-- The overlap transition is an isomorphism. -/
theorem t_id (i : D.J) : D.t i i = 𝟙 _ :=
  D.P.t_id i

/-- Cocycle data for the chart presentation. -/
theorem cocycle (i j k : D.J) :
    D.P.t' i j k ≫ D.P.t' j k i ≫ D.P.t' k i j = 𝟙 _ :=
  D.P.cocycle i j k

/-- The chart presentation packaged as glued quotient data. -/
noncomputable def toGlobalGluedQuotientData : GlobalGluedQuotientData S :=
  { P := D.P, hq := D.hq, hfin := D.hfin }

/-- The cover of the packaged data agrees with the presentation cover. -/
theorem toGlobalGluedQuotientData_cover :
    D.toGlobalGluedQuotientData.cover = D.cover := rfl

/-- A compatible family of maps on the charts induces a map from the glued
quotient scheme. -/
noncomputable def desc {Z : Scheme.{u}} (f : ∀ i : D.J, D.U i ⟶ Z)
    (hf : ∀ i j : D.J,
      pullback.fst ((D.toSchemeGlueData).ι i) ((D.toSchemeGlueData).ι j) ≫ f i =
      pullback.snd ((D.toSchemeGlueData).ι i) ((D.toSchemeGlueData).ι j) ≫ f j) :
    D.glued ⟶ Z :=
  D.P.descOfCompatible Z f hf

/-- Fac equation for the chart descent map. -/
theorem desc_fac {Z : Scheme.{u}} (f : ∀ i : D.J, D.U i ⟶ Z)
    (hf : ∀ i j : D.J,
      pullback.fst ((D.toSchemeGlueData).ι i) ((D.toSchemeGlueData).ι j) ≫ f i =
      pullback.snd ((D.toSchemeGlueData).ι i) ((D.toSchemeGlueData).ι j) ≫ f j)
    (i : D.J) :
    D.chartι i ≫ D.desc f hf = f i :=
  D.P.descOfCompatible_ι Z f hf i

/-- Uniqueness for the chart descent map. -/
theorem desc_uniq {Z : Scheme.{u}} (f : ∀ i : D.J, D.U i ⟶ Z)
    (hf : ∀ i j : D.J,
      pullback.fst ((D.toSchemeGlueData).ι i) ((D.toSchemeGlueData).ι j) ≫ f i =
      pullback.snd ((D.toSchemeGlueData).ι i) ((D.toSchemeGlueData).ι j) ≫ f j)
    (u : D.glued ⟶ Z) (hu : ∀ i : D.J, D.chartι i ≫ u = f i) :
    u = D.desc f hf :=
  D.P.descOfCompatible_unique Z f hf u hu

/-- The canonical chart-cover map from the glued quotient scheme to the base. -/
theorem desc_base (h : ∀ i j : D.J,
    pullback.fst ((D.toSchemeGlueData).ι i) ((D.toSchemeGlueData).ι j) ≫ D.q i =
    pullback.snd ((D.toSchemeGlueData).ι i) ((D.toSchemeGlueData).ι j) ≫ D.q j) :
    D.desc D.q h = D.gluedMap := by
  apply D.desc_uniq D.q h
  intro i
  exact D.desc_fac D.q h i

end GlobalQuotientChartPresentation

namespace GlobalQuotientChartPresentation

variable {S : Scheme.{u}} (D : GlobalQuotientChartPresentation S)

/-- The first projection of the overlap pullback. -/
abbrev overlapFst (i j : D.J) :
    pullback (D.chartι i) (D.chartι j) ⟶ D.U i :=
  pullback.fst (D.chartι i) (D.chartι j)

/-- The second projection of the overlap pullback. -/
abbrev overlapSnd (i j : D.J) :
    pullback (D.chartι i) (D.chartι j) ⟶ D.U j :=
  pullback.snd (D.chartι i) (D.chartι j)

/-- The chart-cover comparison map: from each chart to the glued quotient. -/
noncomputable def chartCoverMap (i : D.J) : D.U i ⟶ D.cover.carrier :=
  D.chartMap i

/-- The chart-cover comparison factors through the glued map. -/
theorem chartCoverMap_fac (i : D.J) :
    D.chartCoverMap i ≫ FiniteEtaleCover.structureMap D.cover = D.q i :=
  D.chartMap_structureMap i

/-- The chart maps are jointly covering: every point of the glued scheme lies in
some chart. -/
theorem chart_cover_joint (x : D.glued) :
    ∃ (i : D.J) (y : D.U i), D.chartι i y = x := by
  classical
  exact (D.toSchemeGlueData).openCover.exists_eq x

/-- The glued quotient scheme is covered by the affine quotient charts. -/
theorem glued_covered_by_affine (x : D.glued) :
    ∃ (i : D.J) (y : D.U i), D.chartι i y = x :=
  D.chart_cover_joint x

/-- The chart presentation gives a morphism from the glued quotient to any
finite etale cover whose charts receive compatible maps. -/
noncomputable def coverDesc {Z : Scheme.{u}} (f : ∀ i : D.J, D.U i ⟶ Z)
    (hf : ∀ i j : D.J,
      pullback.fst ((D.toSchemeGlueData).ι i) ((D.toSchemeGlueData).ι j) ≫ f i =
      pullback.snd ((D.toSchemeGlueData).ι i) ((D.toSchemeGlueData).ι j) ≫ f j) :
    D.cover.carrier ⟶ Z :=
  D.desc f hf

/-- Fac for the cover-level chart descent map. -/
theorem coverDesc_fac {Z : Scheme.{u}} (f : ∀ i : D.J, D.U i ⟶ Z)
    (hf : ∀ i j : D.J,
      pullback.fst ((D.toSchemeGlueData).ι i) ((D.toSchemeGlueData).ι j) ≫ f i =
      pullback.snd ((D.toSchemeGlueData).ι i) ((D.toSchemeGlueData).ι j) ≫ f j)
    (i : D.J) :
    D.chartMap i ≫ D.coverDesc f hf = f i :=
  D.desc_fac f hf i

/-- Uniqueness for the cover-level chart descent map. -/
theorem coverDesc_uniq {Z : Scheme.{u}} (f : ∀ i : D.J, D.U i ⟶ Z)
    (hf : ∀ i j : D.J,
      pullback.fst ((D.toSchemeGlueData).ι i) ((D.toSchemeGlueData).ι j) ≫ f i =
      pullback.snd ((D.toSchemeGlueData).ι i) ((D.toSchemeGlueData).ι j) ≫ f j)
    (u : D.cover.carrier ⟶ Z) (hu : ∀ i : D.J, D.chartMap i ≫ u = f i) :
    u = D.coverDesc f hf :=
  D.desc_uniq f hf u hu

end GlobalQuotientChartPresentation

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartPresentation
