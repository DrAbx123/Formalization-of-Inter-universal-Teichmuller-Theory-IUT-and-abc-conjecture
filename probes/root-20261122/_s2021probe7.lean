import tmp.sheaf.xif.paper.S2012EffectivityComparisonActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option pp.proofs false

namespace Probe

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

abbrev K := S1726K
abbrev Site := SchemeOverField K

abbrev U (S : Site) : LocallyDiscrete Siteᵒᵖ :=
  LocallyDiscrete.mk (Opposite.op S)

variable {F G : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
  (α : Pseudofunctor.StrongTrans F G) {S : Site} {R : Sieve S} (M : F.obj (U S))

section Test
variable {Y : Site} (i₂ : R.arrows.category) (f₂ : Y ⟶ i₂.obj.left)

example : 𝟙 ((G.map f₂.op.toLoc).toFunctor.obj
      ((α.app (U i₂.obj.left)).toFunctor.obj ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M)))
    = 𝟙 (((α.app (U i₂.obj.left) ≫ G.map f₂.op.toLoc).toFunctor).obj
        ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M)) := by rfl

example : 𝟙 ((G.map f₂.op.toLoc).toFunctor.obj
      ((α.app (U i₂.obj.left)).toFunctor.obj ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M)))
    = 𝟙 (((α.app (U i₂.obj.left) ≫ G.map f₂.op.toLoc).toFunctor).obj
        ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M)) := by
  congr 1

example : 𝟙 ((G.map f₂.op.toLoc).toFunctor.obj
      ((α.app (U i₂.obj.left)).toFunctor.obj ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M)))
    = 𝟙 (((α.app (U i₂.obj.left) ≫ G.map f₂.op.toLoc).toFunctor).obj
        ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M)) := by
  simp only [Functor.comp_obj]

end Test

end Probe
