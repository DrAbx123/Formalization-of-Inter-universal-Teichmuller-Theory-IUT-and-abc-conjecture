import tmp.sheaf.xif.paper.S2074IsoCommaTwoPullbackActual

/-! # S2076: fixed site API needed beyond S1832Bicone

To generalize S1985's `liftApp`/`liftNatIso` from bicones to arbitrary
`S2074GeneralCone`s, the first missing API is the component iso of a
`StrongTrans.Modification` at a test object, together with the transport along
`Pseudofunctor.StrongTrans.comp_app`.  The tree has no instance
`IsIso (c.commutes.hom.as.app U)`.

Below the required statements are recorded as Type-valued data; no inhabitant
is asserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2076GeneralLiftAPIGapActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2074IsoCommaTwoPullbackActual

universe u

variable {A B C : S1728Cover}
variable (f : S1728CoverMap A C) (g : S1728CoverMap B C)

/-- Missing API 1: the component of `c.commutes` at U as an iso of the two
composite strong transformations. -/
def S2076ComponentIsoStatement : Type 1 :=
  ∀ (c : S2074GeneralCone f g)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ),
    Iso ((c.toA.vcomp f.map).app U) ((c.toB.vcomp g.map).app U)

/-- Missing API 2: the transported cone at a test object. -/
def S2076ConeAtStatement : Type 1 :=
  ∀ (c : S2074GeneralCone f g)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ),
    S1893Cone (f.map.app U).toFunctor (g.map.app U).toFunctor
      ↑(c.W.obj U)

/-- Missing API 3: the fibre-level lifted functor at a test object. -/
def S2076LiftAppStatement : Type 1 :=
  ∀ (c : S2074GeneralCone f g)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ),
    ↑(c.W.obj U) ⥤
      S1836IsoComma (f.map.app U).toFunctor (g.map.app U).toFunctor

/-- Missing API 4 (the whole site-level lift): the strong transformation
`W -> sitePseudofunctor f g`, its two projections and the full witness. -/
def S2076SiteLiftStatement : Type 1 :=
  ∀ (c : S2074GeneralCone f g),
    Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g)

#check S2076ComponentIsoStatement
#check S2076ConeAtStatement
#check S2076LiftAppStatement
#check S2076SiteLiftStatement

end LeanFormal.IUT.XiFPaper.S2076GeneralLiftAPIGapActual

end
