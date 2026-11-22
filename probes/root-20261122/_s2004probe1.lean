import tmp.sheaf.xif.paper.S1998IsoCommaPrestackActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2004IsoCommaEffectivityActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual
open LeanFormal.IUT.XiFPaper.S1956IsoCommaStackActual
open LeanFormal.IUT.XiFPaper.S1998IsoCommaPrestackActual

universe u

abbrev K := S1726K
abbrev Site := SchemeOverField K
abbrev J : GrothendieckTopology Site := SchemeOverField.etaleTopology K

abbrev U (S : Site) : LocallyDiscrete Siteᵒᵖ :=
  LocallyDiscrete.mk (Opposite.op S)

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
  {S : Site} {R : Sieve S}

/-- The family of arrows of a sieve. -/
abbrev Rfam (R : Sieve S) : R.arrows.category → Site := fun i => i.obj.left

/-- The descent datum of the A-fibre underlying a descent datum of the iso-comma. -/
noncomputable def S2004FstDescentData
    (D : (sitePseudofunctor f g).DescentData (fun (i : R.arrows.category) => i.obj.hom)) :
    A.source.fiber.DescentData (fun (i : R.arrows.category) => i.obj.hom) where
  obj i := (D.obj i).obj.left
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
    (S1836IsoCommaFst (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
      (D.hom q f₁ f₂ hf₁ hf₂)
  pullHom_hom := by sorry
  hom_self := by sorry
  hom_comp := by sorry

#check @S2004FstDescentData

-- Goal state of pullHom_hom field
set_option pp.universes false in
example {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    {S : Site} {R : Sieve S}
    (D : (sitePseudofunctor f g).DescentData (fun (i : R.arrows.category) => i.obj.hom))
    {Y' Y : Site} (gg : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S) (hq : gg ≫ q = q')
    {i₁ i₂ : R.arrows.category} (f₁ : Y ⟶ i₁.obj.left) (f₂ : Y ⟶ i₂.obj.left)
    (hf₁ : f₁ ≫ i₁.obj.hom = q) (hf₂ : f₂ ≫ i₂.obj.hom = q)
    (gf₁ : Y' ⟶ i₁.obj.left) (gf₂ : Y' ⟶ i₂.obj.left)
    (hgf₁ : gg ≫ f₁ = gf₁) (hgf₂ : gg ≫ f₂ = gf₂) : True := by
  have hD := D.pullHom_hom gg q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  have h2 := congrArg (fun m =>
    (S1836IsoCommaFst (f.map.app (U Y')).toFunctor (g.map.app (U Y')).toFunctor).map m) hD
  trace_state
  trivial

#check @Pseudofunctor.LocallyDiscreteOpToCat.pullHom
#check @Pseudofunctor.DescentData.ofObj
#check @Pseudofunctor.DescentData.isoMk
#check @Pseudofunctor.DescentData.Hom
#check @Pseudofunctor.DescentData.toDescentData
#check @CategoryTheory.Pseudofunctor.DescentData.iso
#check @Pseudofunctor.mapComp'_eq_mapComp
#check @Pseudofunctor.mapComp'_inv_naturality
#check @Pseudofunctor.mapComp'_hom_naturality
#check @Pseudofunctor.mapComp'_comp_id_hom_app
#check @Functor.FullyFaithful.preimageIso
#check @Functor.preimageIso
#check @Functor.FullyFaithful.map_preimageIso

end LeanFormal.IUT.XiFPaper.S2004IsoCommaEffectivityActual
