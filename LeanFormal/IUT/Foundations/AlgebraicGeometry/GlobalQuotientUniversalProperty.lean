import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientGluedCover
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
import Mathlib.CategoryTheory.Limits.Shapes.SingleObj

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientUniversalProperty

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {S : Scheme.{u}}

/-- Glued global quotient data: affine-local quotient preglue data together with
the compatibility of the chart maps and finiteness of the glued structure map. -/
structure GlobalGluedQuotientData (S : Scheme.{u}) where
  P : AffineLocalQuotientPreglueData S
  hq : ∀ i j : P.J,
    pullback.fst ((P.toSchemeGlueData).ι i) ((P.toSchemeGlueData).ι j) ≫ P.q i =
      pullback.snd ((P.toSchemeGlueData).ι i) ((P.toSchemeGlueData).ι j) ≫ P.q j
  hfin : IsFinite (P.gluedMapOfCompatible hq)

namespace GlobalGluedQuotientData

variable (D : GlobalGluedQuotientData S)

/-- The actual glued global quotient cover. -/
noncomputable def cover : FiniteEtaleCover S :=
  D.P.toFiniteEtaleCoverOfIsFinite D.hq D.hfin

/-- The structure map of the glued quotient cover. -/
noncomputable def structureMap : D.cover.carrier ⟶ S :=
  D.P.gluedMapOfCompatible D.hq

theorem structureMap_eq : D.structureMap = D.cover.structureMap :=
  rfl

/-- The universal property desc: compatible local chart morphisms glue to a
morphism out of the global glued quotient. -/
noncomputable def desc (Z : Scheme.{u})
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j) :
    D.cover.carrier ⟶ Z :=
  D.P.descOfCompatible Z f hf

theorem desc_ι (Z : Scheme.{u})
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j)
    (i : D.P.J) :
    (D.P.toSchemeGlueData).ι i ≫ D.desc Z f hf = f i :=
  D.P.descOfCompatible_ι Z f hf i

theorem desc_unique (Z : Scheme.{u})
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
diagram in `FiniteEtaleCover S` should have an actual colimit.  This is stated
as a Prop with no inhabitant and no provider claim. -/
def GlobalQuotientCoconeResidual (S : Scheme.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    HasColimitsOfShape (SingleObj G) (FiniteEtaleCover S)
end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientUniversalProperty
end