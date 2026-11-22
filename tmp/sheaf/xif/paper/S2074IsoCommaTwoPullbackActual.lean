import tmp.sheaf.xif.paper.S2069D6CompositionClosureActual
import tmp.sheaf.xif.paper.S2058D6FiniteEtaleActual
import tmp.sheaf.xif.paper.S1893PullbackUniversalActual
import tmp.sheaf.xif.paper.S1985SiteLiftNaturalityActual

/-! # S2074: iso-comma square 2-universal property: general cone and exact missing

`S2058IsoCommaTwoPullback` asks for the full `TwoPullbackWitness` of the
iso-comma square `(toA, toB, f.map, g.map)`.  The tree contains:
* the fibre-level universal property `S1893Lift` (for every cone of functors);
* the site-level lift `S1985.liftSite` only for the *bicones* `S1832Bicone`
  arising from actual covers `W`.

The general pseudo-cone is `S2074GeneralCone`: any pseudofunctor `W` with
arbitrary strong transformations `toA : W -> A.source.fiber`,
`toB : W -> B.source.fiber` and a 2-cell iso of composites.  The missing part
is the site-level strong transformation `W -> sitePseudofunctor f g` and its
four coherence fields; the fibre level is available.

No witness is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2074IsoCommaTwoPullbackActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S1985SiteLiftNaturalityActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual

universe u

variable {A B C : S1728Cover}
variable (f : S1728CoverMap A C) (g : S1728CoverMap B C)

/-- A general pseudo-cone over the cospan `(f, g)` of cover maps. -/
structure S2074GeneralCone where
  W : EtaleStackPseudofunctor S1726K
  toA : Pseudofunctor.StrongTrans W A.source.fiber
  toB : Pseudofunctor.StrongTrans W B.source.fiber
  commutes : Iso (Pseudofunctor.StrongTrans.vcomp toA f.map)
    (Pseudofunctor.StrongTrans.vcomp toB g.map)

/-- The exact site-level statement: the iso-comma square has the full
2-universal property for every cospan of actual covers. -/
def S2074IsoCommaTwoPullbackStatement : Type 1 :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C),
    (EtalePseudofunctorSquare.mk (toA f g) (toB f g) f.map g.map
      (commutes f g)).TwoPullbackWitness

/-- The statement is exactly the S2058 first-missing input (same term). -/
def S2074SameAsS2058 : Type 1 :=
  S2074IsoCommaTwoPullbackStatement

/-! ## Exact missing lemma list

1. `generalLiftApp` (actual, fibre level): for `c : S2074GeneralCone f g` and
   each `U`, `S1893Lift (f.map.app U).toFunctor (g.map.app U).toFunctor
   (coneAt c U)`, where `coneAt c U` has toA = `(c.toA.app U).toFunctor`,
   toB = `(c.toB.app U).toFunctor`, and commutes = the component of
   `c.commutes.hom` (a `StrongTrans.Modification`) at `U`, transported across
   `Pseudofunctor.StrongTrans.comp_app`.
2. `generalLiftNat` (missing): for each site morphism `φ : U ⟶ V`, a natural
   iso between `(W.fiber.map φ).toFunctor ⋙ liftApp U` and
   `liftApp V ⋙ (S1890IsoCommaMap f g φ).toFunctor`; built from
   `c.toA.naturality φ`, `c.toB.naturality φ`, `c.commutes` and S1893's
   `S1893ComparisonFunctor` — the analogue of S1985 `liftNatIso`, which is
   proved only for `S1832Bicone`.
3. `generalLiftNat` coherence (missing): `naturality_naturality`,
   `naturality_id`, `naturality_comp` — the analogues of S1985's
   `liftNatConeA/B` and `liftNatIso` coherence, but for arbitrary cones.
4. `liftToA` / `liftToB` (missing): the composites with `toA` / `toB`; fibre
   components are `S1893Lift_fst` / `S1893Lift_snd`, site-level naturality
   follows from (2).
5. `liftTwoCell` / `_toA` / `_toB` (missing): functoriality on cone morphisms;
   fibre level is `S1893ComparisonFunctor`/`S1893LiftUniq`, site level needs the
   modification naturality from (3).
6. `twoCell_ext` (available): for two 2-cells between lifts, joint
   faithfulness of `toA`, `toB` follows from `S1836IsoComma_hom_ext` and the
   lift app functors' first/second projections.

Items 2-5 are the exact site-level content absent from the tree; S1985 covers
them only for bicones, and S1893 only at a single test object. -/

#check S2074GeneralCone
#check S2074IsoCommaTwoPullbackStatement

end LeanFormal.IUT.XiFPaper.S2074IsoCommaTwoPullbackActual

end
