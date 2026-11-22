import tmp.sheaf.xif.paper.S2078ConeAtLiftAppActual

/-! # S2079: general lift naturality, first two cone comparisons

Mirrors S1985 `liftNatConeA/B`, `cone1_commutes_app`, `cone2_commutes_app`
for an arbitrary `S2074GeneralCone`.  Uses S2078 `S2078ConeAt/LiftApp`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2079GeneralLiftNatActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual
open LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2074IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2077ComponentIsoActual
open LeanFormal.IUT.XiFPaper.S2078ConeAtLiftAppActual

universe u
variable {A B C : S1728Cover}
variable (f : S1728CoverMap A C) (g : S1728CoverMap B C)

noncomputable def S2079LiftNatConeA (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    (((c.W.map φ).toFunctor ⋙ S2078LiftApp f g c V) ⋙
        S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor) ⟶
      ((S2078LiftApp f g c U ⋙ (S1890IsoCommaMap f g φ).toFunctor) ⋙
        S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor) :=
  (c.toA.naturality φ).hom.toNatTrans

noncomputable def S2079LiftNatConeB (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    (((c.W.map φ).toFunctor ⋙ S2078LiftApp f g c V) ⋙
        S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor) ⟶
      ((S2078LiftApp f g c U ⋙ (S1890IsoCommaMap f g φ).toFunctor) ⋙
        S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor) :=
  (c.toB.naturality φ).hom.toNatTrans

#print axioms S2079LiftNatConeA

end LeanFormal.IUT.XiFPaper.S2079GeneralLiftNatActual

end
