import tmp.sheaf.xif.paper.S2079GeneralLiftNatActual

/-! # S2080: app-level eqToIso and the ConeAt commutativity lemma

Implements the app-level reduction needed for `S2079cone1_commutes_app`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2080ConeAtCommutesActual

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
open LeanFormal.IUT.XiFPaper.S2077ComponentIsoActual
open LeanFormal.IUT.XiFPaper.S2078ConeAtLiftAppActual
open LeanFormal.IUT.XiFPaper.S2079GeneralLiftNatActual

universe u
variable {A B C : S1728Cover}
variable (f : S1728CoverMap A C) (g : S1728CoverMap B C)

/-- App-level form of `eqToIso`. -/
theorem S2080_eqToIso_app {D E : Type u} [Category.{u} D] [Category.{u} E]
    {F G : D ⥤ E} (h : F = G) (x : D) :
    (CategoryTheory.eqToIso h).app x =
      CategoryTheory.eqToIso (congrArg (fun F => F.obj x) h) := by
  cases h
  rfl

#print axioms S2080_eqToIso_app

/-- Hom-level form of `eqToIso` app. -/
theorem S2080_eqToIso_app_hom {D E : Type u} [Category.{u} D] [Category.{u} E]
    {F G : D ⥤ E} (h : F = G) (x : D) :
    ((CategoryTheory.eqToIso h).app x).hom =
      CategoryTheory.eqToHom (congrArg (fun F => F.obj x) h) := by
  cases h
  rfl

/-- App-level commutativity of `S2078ConeAt.commutes`. -/
theorem S2080ConeAt_commutes_app (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (x : ↑(c.W.obj U)) :
    ((S2078ConeAt f g c V).commutes.app ((c.W.map φ).toFunctor.obj x)).hom =
      (c.commutes.hom.as.app V).toNatTrans.app ((c.W.map φ).toFunctor.obj x) := by
  dsimp only [S2078ConeAt, S2077ComponentIso, CategoryTheory.Cat.Hom.toNatIso]
  rw [NatIso.trans_app, NatIso.trans_app]
  rw [Iso.trans_hom, Iso.trans_hom]
  rw [S2080_eqToIso_app_hom, S2080_eqToIso_app_hom]
  simp only [Category.assoc, eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

#print axioms S2080ConeAt_commutes_app


end LeanFormal.IUT.XiFPaper.S2080ConeAtCommutesActual

end
