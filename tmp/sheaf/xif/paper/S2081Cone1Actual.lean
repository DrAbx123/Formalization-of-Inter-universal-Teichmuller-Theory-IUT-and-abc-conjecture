import tmp.sheaf.xif.paper.S2080ConeAtCommutesActual

/-! # S2081: cone1 commutativity from S2080

Restores S1985's `cone1_commutes_app` for a general `S2074GeneralCone`,
using `S2080ConeAt_commutes_app`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2081Cone1Actual

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
open LeanFormal.IUT.XiFPaper.S2078ConeAtLiftAppActual
open LeanFormal.IUT.XiFPaper.S2080ConeAtCommutesActual

universe u
variable {A B C : S1728Cover}
variable (f : S1728CoverMap A C) (g : S1728CoverMap B C)

theorem S2081cone1_commutes_app (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (x : ↑(c.W.obj U)) :
    ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↑(c.W.obj U)).obj
          ((c.W.map φ).toFunctor ⋙ S2078LiftApp f g c V)).commutes.hom.app x =
      (c.commutes.hom.as.app V).toNatTrans.app ((c.W.map φ).toFunctor.obj x) := by
  rw [S1893ComparisonFunctor_obj_commutes_hom_app, S1836IsoCommaNatIso_hom_app]
  change ((S2078LiftApp f g c V).obj ((c.W.map φ).toFunctor.obj x)).obj.hom = _
  simp only [S2078LiftApp]
  rw [S1893Lift_structure]
  exact S2080ConeAt_commutes_app f g c φ x

#print axioms S2081cone1_commutes_app

end LeanFormal.IUT.XiFPaper.S2081Cone1Actual

end
