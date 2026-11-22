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

variable (D : (sitePseudofunctor f g).DescentData (fun (i : R.arrows.category) => i.obj.hom))
  (a : A.source.fiber.obj (U S))
  (eA : (Pseudofunctor.toDescentData A.source.fiber (fun (i : R.arrows.category) => i.obj.hom)).obj a
      ≅ S2004FstDescentData f g D)
  (b : B.source.fiber.obj (U S))
  (eB : (Pseudofunctor.toDescentData B.source.fiber (fun (i : R.arrows.category) => i.obj.hom)).obj b
      ≅ S2004SndDescentData f g D)

/-- The f-side comparison of C-descent data. -/
noncomputable def S2026MidIsoF :
    (Pseudofunctor.toDescentData C.source.fiber (fun (i : R.arrows.category) => i.obj.hom)).obj
        ((f.map.app (U S)).toFunctor.obj a) ≅ S2004MidF f g D :=
  S2021PushComparison (R := R) f.map a ≪≫ S2021PushFunctorialityIso (R := R) f.map eA

/-- The g-side comparison of C-descent data. -/
noncomputable def S2026MidIsoG :
    (Pseudofunctor.toDescentData C.source.fiber (fun (i : R.arrows.category) => i.obj.hom)).obj
        ((g.map.app (U S)).toFunctor.obj b) ≅ S2004MidG f g D :=
  S2021PushComparison (R := R) g.map b ≪≫ S2021PushFunctorialityIso (R := R) g.map eB

/-- The composite comparison through the middle. -/
noncomputable def S2026Theta :
    (Pseudofunctor.toDescentData C.source.fiber (fun (i : R.arrows.category) => i.obj.hom)).obj
        ((f.map.app (U S)).toFunctor.obj a) ≅
      (Pseudofunctor.toDescentData C.source.fiber (fun (i : R.arrows.category) => i.obj.hom)).obj
        ((g.map.app (U S)).toFunctor.obj b) :=
  S2026MidIsoF (D := D) (a := a) (eA := eA) ≪≫ S2004MidComparison f g D
    ≪≫ (S2026MidIsoG (D := D) (b := b) (eB := eB)).symm

theorem S2026MidIsoF_hom (i : R.arrows.category) :
    (S2026MidIsoF (D := D) (a := a) (eA := eA)).hom.hom i =
      ((Cat.Hom.toNatIso (f.map.naturality (i.obj.hom.op.toLoc))).symm.app a).hom
        ≫ (f.map.app (U i.obj.left)).toFunctor.map (eA.hom.hom i) := by
  rfl

theorem S2026MidIsoG_hom (i : R.arrows.category) :
    (S2026MidIsoG (D := D) (b := b) (eB := eB)).hom.hom i =
      (S1864SiteComparisonRight g (i.obj.hom.op.toLoc)).hom.app b
        ≫ (g.map.app (U i.obj.left)).toFunctor.map (eB.hom.hom i) := by
  rfl

theorem S2026MidComparison_hom (i : R.arrows.category) :
    (S2004MidComparison f g D).hom.hom i = (D.obj i).obj.hom := by
  rfl

end Core
end LeanFormal.IUT.XiFPaper.S2026Probe
