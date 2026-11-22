import tmp.sheaf.xif.paper.S2077ComponentIsoActual

/-! # S2078: transported cone and fibre-level lift for a general cone

Uses `S2077ComponentIso` and `Pseudofunctor.StrongTrans.comp_app` to build
the S1893 cone at a test object, then `S1893Lift` gives the fibre-level lifted
functor.  This realizes `S2076ConeAtStatement` and `S2076LiftAppStatement`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2078ConeAtLiftAppActual

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
open LeanFormal.IUT.XiFPaper.S2076GeneralLiftAPIGapActual
open LeanFormal.IUT.XiFPaper.S2077ComponentIsoActual

universe u

variable {A B C : S1728Cover}
variable (f : S1728CoverMap A C) (g : S1728CoverMap B C)

/-- The S1893 cone at a test object, with the comparison transported along
`StrongTrans.comp_app`. -/
noncomputable def S2078ConeAt (c : S2074GeneralCone f g)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    S1893Cone (f.map.app U).toFunctor (g.map.app U).toFunctor
      ↑(c.W.obj U) where
  toA := (c.toA.app U).toFunctor
  toB := (c.toB.app U).toFunctor
  commutes :=
    (CategoryTheory.eqToIso (congrArg CategoryTheory.Cat.Hom.toFunctor
      (Pseudofunctor.StrongTrans.comp_app c.toA f.map U)).symm).trans
      ((CategoryTheory.Cat.Hom.toNatIso (S2077ComponentIso f g c U)).trans
        (CategoryTheory.eqToIso (congrArg CategoryTheory.Cat.Hom.toFunctor
          (Pseudofunctor.StrongTrans.comp_app c.toB g.map U))))

/-- The fibre-level lifted functor at a test object. -/
noncomputable def S2078LiftApp (c : S2074GeneralCone f g)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    ↑(c.W.obj U) ⥤
      S1836IsoComma (f.map.app U).toFunctor (g.map.app U).toFunctor :=
  S1893Lift (f.map.app U).toFunctor (g.map.app U).toFunctor (S2078ConeAt f g c U)

#print axioms S2078ConeAt
#print axioms S2078LiftApp

end LeanFormal.IUT.XiFPaper.S2078ConeAtLiftAppActual

end
