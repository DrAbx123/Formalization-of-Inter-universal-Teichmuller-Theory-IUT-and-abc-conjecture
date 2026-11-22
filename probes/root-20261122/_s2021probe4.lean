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

example :
    (Pseudofunctor.toDescentData G (fun (i : R.arrows.category) => i.obj.hom)).obj
        ((α.app (U S)).toFunctor.obj M) ≅
      S2004PushDescentData (R := R) α
        ((Pseudofunctor.toDescentData F (fun (i : R.arrows.category) => i.obj.hom)).obj M) :=
  Pseudofunctor.DescentData.isoMk
    (fun i => (Cat.Hom.toNatIso (α.naturality ((i.obj.hom).op.toLoc))).symm.app M)
    (by
      intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
      dsimp only [Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj,
        S2004PushDescentData]
      trace_state
      sorry)

end Probe
