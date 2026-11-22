import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientUniq
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Global glued quotient assembly

This file builds an actual `GlobalGluedQuotientData` from affine chart data for
a global finite etale cover with finite group action.  The chart fields are the
actual local quotient charts and their gluing data; the resulting glued cover
is finite etale over the base and has the previously proved desc/fac/uniq
universal property.

The file is a post-compile-delta draft and is held for the next batch; no
provider or colimit is asserted.
-/

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalGluedQuotientAssembly

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDesc
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientFac
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientUniq
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {S : Scheme.{u}}

/-- Affine chart data for the global quotient assembly: actual local quotient
charts and their gluing intersections/transitions. -/
structure AffineGlobalQuotientChartAssembly (S : Scheme.{u}) where
  /-- Index type of affine local quotient charts. -/
  J : Type u
  /-- Local quotient charts. -/
  U : J → Scheme.{u}
  /-- Chart intersections. -/
  V : J × J → Scheme.{u}
  /-- Intersection projections to the left chart. -/
  f : ∀ i j, V (i, j) ⟶ U i
  /-- The intersection projections are open immersions. -/
  f_open : ∀ i j, IsOpenImmersion (f i j)
  /-- Pullbacks of intersection projections exist. -/
  f_hasPullback : ∀ i j k, HasPullback (f i j) (f i k)
  /-- Diagonal intersection projections are isomorphisms. -/
  f_id : ∀ i, IsIso (f i i)
  /-- Transition maps. -/
  t : ∀ i j, V (i, j) ⟶ V (j, i)
  /-- Diagonal transitions are identities. -/
  t_id : ∀ i, t i i = 𝟙 _
  /-- Triple-overlap transitions. -/
  t' : ∀ i j k, pullback (f i j) (f i k) ⟶ pullback (f j k) (f j i)
  /-- Facet compatibility. -/
  t_fac : ∀ i j k, t' i j k ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t i j
  /-- Cocycle condition. -/
  cocycle : ∀ i j k, t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _
  /-- Chart maps to the base. -/
  q : ∀ i, U i ⟶ S
  /-- Chart maps are etale. -/
  q_etale : ∀ i, Etale (q i)

namespace AffineGlobalQuotientChartAssembly

variable (A : AffineGlobalQuotientChartAssembly S)

/-- The preglue data assembled from the affine chart data. -/
noncomputable def toPreglueData : AffineLocalQuotientPreglueData S where
  J := A.J
  U := A.U
  V := A.V
  f := A.f
  f_open := A.f_open
  f_hasPullback := A.f_hasPullback
  f_id := A.f_id
  t := A.t
  t_id := A.t_id
  t' := A.t'
  t_fac := A.t_fac
  cocycle := A.cocycle
  q := A.q
  q_etale := A.q_etale

/-- The actual global glued quotient data assembled from affine chart data,
given the chart-map compatibility and the finiteness of the glued structure map. -/
noncomputable def toGlobalGluedQuotientData
    (hq : ∀ i j : A.J,
      pullback.fst ((A.toPreglueData).toSchemeGlueData.ι i)
          ((A.toPreglueData).toSchemeGlueData.ι j) ≫ (A.toPreglueData).q i =
        pullback.snd ((A.toPreglueData).toSchemeGlueData.ι i)
          ((A.toPreglueData).toSchemeGlueData.ι j) ≫ (A.toPreglueData).q j)
    (hfin : IsFinite ((A.toPreglueData).gluedMapOfCompatible hq)) :
    GlobalGluedQuotientData S where
  P := A.toPreglueData
  hq := hq
  hfin := hfin

end AffineGlobalQuotientChartAssembly

namespace GlobalGluedQuotientData

variable (D : GlobalGluedQuotientData S)

/-- The assembled glued quotient cover is etale over the base. -/
theorem assembled_cover_etale : Etale D.cover.structureMap :=
  D.cover_etale

/-- The assembled glued quotient cover is finite over the base. -/
theorem assembled_cover_finite : IsFinite D.cover.structureMap :=
  D.cover_finite

/-- The assembled glued quotient has the desc construction. -/
noncomputable def assembledDesc (Z : Scheme.{u})
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j) :
    D.cover.carrier ⟶ Z :=
  D.desc Z f hf

theorem assembledDesc_ι (Z : Scheme.{u})
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j)
    (i : D.P.J) :
    (D.P.toSchemeGlueData).ι i ≫ GlobalGluedQuotientAssembly.GlobalGluedQuotientData.assembledDesc D Z f hf = f i :=
  GlobalQuotientFac.GlobalGluedQuotientData.desc_ι D Z f hf i

theorem assembledDesc_unique (Z : Scheme.{u})
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j)
    (u : D.cover.carrier ⟶ Z)
    (hu : ∀ i : D.P.J, (D.P.toSchemeGlueData).ι i ≫ u = f i) :
    u = GlobalGluedQuotientAssembly.GlobalGluedQuotientData.assembledDesc D Z f hf :=
  GlobalQuotientUniq.GlobalGluedQuotientData.desc_unique D Z f hf u hu

end GlobalGluedQuotientData

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalGluedQuotientAssembly
end