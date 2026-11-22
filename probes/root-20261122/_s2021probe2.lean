import tmp.sheaf.xif.paper.S2012EffectivityComparisonActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option pp.proofs false
set_option pp.maxSteps 100000

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

example (i : R.arrows.category) :
    ((Pseudofunctor.toDescentData G (fun (i : R.arrows.category) => i.obj.hom)).obj
        ((α.app (U S)).toFunctor.obj M)).obj i ≅
      (S2004PushDescentData (R := R) α
        ((Pseudofunctor.toDescentData F (fun (i : R.arrows.category) => i.obj.hom)).obj M)).obj i :=
  (Cat.Hom.toNatIso (α.naturality ((i.obj.hom).op.toLoc))).symm.app M

-- now the comm field
example (Y : Site) (q : Y ⟶ S) (i₁ i₂ : R.arrows.category) (f₁ : Y ⟶ i₁.obj.left)
    (f₂ : Y ⟶ i₂.obj.left) (hf₁ : f₁ ≫ i₁.obj.hom = q) (hf₂ : f₂ ≫ i₂.obj.hom = q) :
    (G.map f₁.op.toLoc).toFunctor.map
        (show ((Pseudofunctor.toDescentData G (fun (i : R.arrows.category) => i.obj.hom)).obj
            ((α.app (U S)).toFunctor.obj M)).obj i₁ ⟶
          (S2004PushDescentData (R := R) α
            ((Pseudofunctor.toDescentData F (fun (i : R.arrows.category) => i.obj.hom)).obj M)).obj i₁
         from ((Cat.Hom.toNatIso (α.naturality ((i₁.obj.hom).op.toLoc))).symm.app M).hom) ≫
      (S2004PushDescentData (R := R) α
        ((Pseudofunctor.toDescentData F (fun (i : R.arrows.category) => i.obj.hom)).obj M)).hom
          q f₁ f₂ hf₁ hf₂ =
    (Pseudofunctor.toDescentData G (fun (i : R.arrows.category) => i.obj.hom)).obj
          ((α.app (U S)).toFunctor.obj M) |>.hom q f₁ f₂ hf₁ hf₂ ≫
      (G.map f₂.op.toLoc).toFunctor.map
        (show ((Pseudofunctor.toDescentData G (fun (i : R.arrows.category) => i.obj.hom)).obj
            ((α.app (U S)).toFunctor.obj M)).obj i₂ ⟶
          (S2004PushDescentData (R := R) α
            ((Pseudofunctor.toDescentData F (fun (i : R.arrows.category) => i.obj.hom)).obj M)).obj i₂
         from ((Cat.Hom.toNatIso (α.naturality ((i₂.obj.hom).op.toLoc))).symm.app M).hom) := by
  trace_state
  sorry

end Probe
