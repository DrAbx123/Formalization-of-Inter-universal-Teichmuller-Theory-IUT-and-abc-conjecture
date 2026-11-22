import tmp.sheaf.xif.paper.S2021ComparisonFinishActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2026Probe

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1935CatCoherenceActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1956IsoCommaStackActual
open LeanFormal.IUT.XiFPaper.S1998IsoCommaPrestackActual
open LeanFormal.IUT.XiFPaper.S2004IsoCommaEffectivityActual
open LeanFormal.IUT.XiFPaper.S2012EffectivityComparisonActual
open LeanFormal.IUT.XiFPaper.S2021ComparisonFinishActual

universe u
abbrev K := S1726K
abbrev Site := SchemeOverField K
abbrev J : GrothendieckTopology Site := SchemeOverField.etaleTopology K
abbrev U (S : Site) : LocallyDiscrete Siteᵒᵖ := LocallyDiscrete.mk (Opposite.op S)

section Core

variable {A B C : S1728Cover} {f : S1728CoverMap A C} {g : S1728CoverMap B C}
  {S : Site} {R : Sieve S}

#check @NatIso.hom_inv_id_app
#check @NatIso.symm
#check @NatIso.app
#check @Iso.hom_inv_id_app
#check @NatTrans.comp_app
#check @NatTrans.id_app
#check @Iso.symm_apply_apply
#check @CategoryTheory.NatIso.symm_app

example (p : U S ⟶ U S) (a : A.source.fiber.obj (U S)) :
    (S1864SiteComparisonLeft f p).hom.app a
      ≫ ((Cat.Hom.toNatIso (f.map.naturality p)).symm.app a).hom = 𝟙 _ := by
  dsimp only [S1864SiteComparisonLeft]
  sorry

end Core
end LeanFormal.IUT.XiFPaper.S2026Probe
