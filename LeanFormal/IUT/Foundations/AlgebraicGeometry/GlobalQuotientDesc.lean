import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientGluedCover
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
import Mathlib.CategoryTheory.Limits.Shapes.SingleObj

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Global glued quotient: data and desc construction

This file starts the batch for the universal property of the glued global
quotient cover. It uses the production affine-local quotient preglue data and
its scheme-level gluing interface.

The structure `GlobalGluedQuotientData` packages exactly the data needed for
the glued quotient cover: the preglue data `P`, compatibility of the chart
maps on intersections, and finiteness of the glued structure map. The
resulting cover and the desc construction are actual, not fields of a provider
or a placeholder.
-/

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDesc

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {S : Scheme.{u}}

/-- Glued global quotient data: affine-local quotient preglue data together with
the compatibility of the chart maps and finiteness of the glued structure map. -/
structure GlobalGluedQuotientData (S : Scheme.{u}) where
  /-- Affine-local quotient preglue data. -/
  P : AffineLocalQuotientPreglueData S
  /-- Compatibility of the local quotient chart maps on the intersections. -/
  hq : ∀ i j : P.J,
    pullback.fst ((P.toSchemeGlueData).ι i) ((P.toSchemeGlueData).ι j) ≫ P.q i =
      pullback.snd ((P.toSchemeGlueData).ι i) ((P.toSchemeGlueData).ι j) ≫ P.q j
  /-- Finiteness of the glued structure map. -/
  hfin : IsFinite (P.gluedMapOfCompatible hq)

namespace GlobalGluedQuotientData

variable (D : GlobalGluedQuotientData S)

/-- The actual glued global quotient cover, obtained from the production
affine-local quotient packaging. -/
noncomputable def cover : FiniteEtaleCover S :=
  D.P.toFiniteEtaleCoverOfIsFinite D.hq D.hfin

/-- The structure morphism of the glued global quotient cover. -/
noncomputable def structureMap : D.cover.carrier ⟶ S :=
  D.P.gluedMapOfCompatible D.hq

/-- The constructed structure map is exactly the structure map of the cover. -/
theorem structureMap_eq : D.structureMap = D.cover.structureMap :=
  rfl

/-- The carrier of the glued quotient cover is the glued scheme of the preglue
data. -/
theorem cover_carrier_eq : D.cover.carrier = D.P.toSchemeGlueData.glued :=
  rfl

/-- The desc construction: compatible morphisms from the local quotient charts
glue to a morphism out of the actual global quotient cover. -/
noncomputable def desc (Z : Scheme.{u})
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j) :
    D.cover.carrier ⟶ Z :=
  D.P.descOfCompatible Z f hf

/-- The desc construction is the glued morphism supplied by the production
scheme-level gluing interface. -/
theorem desc_def (Z : Scheme.{u})
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j) :
    D.desc Z f hf = D.P.descOfCompatible Z f hf :=
  rfl

/-- The glued quotient cover is etale over the base. -/
theorem cover_etale : Etale D.cover.structureMap :=
  D.cover.etale_structureMap

/-- The glued quotient cover is finite over the base. -/
theorem cover_finite : IsFinite D.cover.structureMap :=
  D.cover.finite_structureMap

/-- The glued structure map is etale. -/
theorem structureMap_etale : Etale D.structureMap :=
  D.P.gluedMapOfCompatible_etale D.hq

/-- The glued structure map is finite. -/
theorem structureMap_finite : IsFinite D.structureMap :=
  D.hfin

/-- Each local quotient chart embeds as an open subscheme of the glued quotient. -/
theorem chart_ι_isOpenImmersion (i : D.P.J) :
    IsOpenImmersion ((D.P.toSchemeGlueData).ι i) :=
  inferInstance

/-- The local quotient charts jointly cover the glued quotient carrier. -/
theorem chart_ι_jointly_surjective :
    ∀ x : D.cover.carrier, ∃ (i : D.P.J) (y : (D.P.U i).carrier),
      (D.P.toSchemeGlueData).ι i y = x :=
  fun x => (D.P.toSchemeGlueData).ι_jointly_surjective x
end GlobalGluedQuotientData

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDesc
end