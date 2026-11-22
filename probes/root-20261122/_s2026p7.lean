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

/-- The component at i of an isomorphism of descent data, as an isomorphism. -/
noncomputable def S2026CompIso {F : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
    {D₁ D₂ : F.DescentData (fun (i : R.arrows.category) => i.obj.hom)} (e : D₁ ≅ D₂)
    (i : R.arrows.category) : D₁.obj i ≅ D₂.obj i where
  hom := e.hom.hom i
  inv := e.inv.hom i
  hom_inv_id := by
    rw [← Pseudofunctor.DescentData.comp_hom, e.hom_inv_id, Pseudofunctor.DescentData.id_hom]
  inv_hom_id := by
    rw [← Pseudofunctor.DescentData.comp_hom, e.inv_hom_id, Pseudofunctor.DescentData.id_hom]

noncomputable def S2026MidIsoF :
    (Pseudofunctor.toDescentData C.source.fiber (fun (i : R.arrows.category) => i.obj.hom)).obj
        ((f.map.app (U S)).toFunctor.obj a) ≅ S2004MidF f g D :=
  S2021PushComparison (R := R) f.map a ≪≫ S2021PushFunctorialityIso (R := R) f.map eA

noncomputable def S2026MidIsoG :
    (Pseudofunctor.toDescentData C.source.fiber (fun (i : R.arrows.category) => i.obj.hom)).obj
        ((g.map.app (U S)).toFunctor.obj b) ≅ S2004MidG f g D :=
  S2021PushComparison (R := R) g.map b ≪≫ S2021PushFunctorialityIso (R := R) g.map eB

noncomputable def S2026Theta :
    (Pseudofunctor.toDescentData C.source.fiber (fun (i : R.arrows.category) => i.obj.hom)).obj
        ((f.map.app (U S)).toFunctor.obj a) ≅
      (Pseudofunctor.toDescentData C.source.fiber (fun (i : R.arrows.category) => i.obj.hom)).obj
        ((g.map.app (U S)).toFunctor.obj b) :=
  S2026MidIsoF (D := D) (a := a) (eA := eA) ≪≫ S2004MidComparison f g D
    ≪≫ (S2026MidIsoG (D := D) (b := b) (eB := eB)).symm

/-- The C-side fully faithful comparison. -/
noncomputable def S2026CFF (hR : R ∈ J S) :
    (Pseudofunctor.toDescentData C.source.fiber
      (fun (i : R.arrows.category) => i.obj.hom)).FullyFaithful :=
  letI := C.source.isStack.toIsPrestack
  (C.source.fiber.isPrestackFor' R hR).fullyFaithful

/-- The isomorphism in the C-fibre produced by full faithfulness. -/
noncomputable def S2026PsiIso (hR : R ∈ J S) :
    ((f.map.app (U S)).toFunctor.obj a) ≅ ((g.map.app (U S)).toFunctor.obj b) :=
  (S2026CFF (C := C) (R := R) hR).preimageIso
    (S2026Theta (D := D) (a := a) (eA := eA) (b := b) (eB := eB))

/-- The reassembled iso-comma object. -/
noncomputable def S2026X (hR : R ∈ J S) : (sitePseudofunctor f g).obj (U S) :=
  ⟨Comma.mk a b (S2026PsiIso (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).hom,
    (S2026PsiIso (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).isIso_hom⟩

theorem S2026PsiIso_map (hR : R ∈ J S) :
    (Pseudofunctor.toDescentData C.source.fiber
      (fun (i : R.arrows.category) => i.obj.hom)).map
        (S2026PsiIso (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).hom
      = (S2026Theta (D := D) (a := a) (eA := eA) (b := b) (eB := eB)).hom :=
  (S2026CFF (C := C) (R := R) hR).map_preimage _

theorem S2026ComponentSquare (hR : R ∈ J S) (i : R.arrows.category) :
    (f.map.app (U i.obj.left)).toFunctor.map (eA.hom.hom i) ≫ (D.obj i).obj.hom
      = (((sitePseudofunctor f g).map (i.obj.hom.op.toLoc)).toFunctor.obj
            (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)).obj.hom
          ≫ (g.map.app (U i.obj.left)).toFunctor.map (eB.hom.hom i) := by
  sorry

theorem S2026X_objHom (hR : R ∈ J S) (i : R.arrows.category) :
    (((sitePseudofunctor f g).map (i.obj.hom.op.toLoc)).toFunctor.obj
        (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)).obj.hom
      = (S1864SiteComparisonLeft f (i.obj.hom.op.toLoc)).hom.app a
        ≫ (C.source.fiber.map (i.obj.hom.op.toLoc)).toFunctor.map
            (S2026PsiIso (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).hom
        ≫ (S1864SiteComparisonRight g (i.obj.hom.op.toLoc)).hom.app b := by
  have h := S1998ObjHom f g (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)
    (Opposite.op (Over.mk i.obj.hom))
  simpa only [Opposite.unop_op] using h

theorem S2026PsiIso_map_app (hR : R ∈ J S) (i : R.arrows.category) :
    ((Pseudofunctor.toDescentData C.source.fiber
      (fun (i : R.arrows.category) => i.obj.hom)).map
        (S2026PsiIso (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).hom).hom i
      = (C.source.fiber.map (i.obj.hom.op.toLoc)).toFunctor.map
        (S2026PsiIso (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).hom := rfl

theorem S2026PsiIso_map_eq (hR : R ∈ J S) (i : R.arrows.category) :
    (C.source.fiber.map (i.obj.hom.op.toLoc)).toFunctor.map
        (S2026PsiIso (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).hom
      = (S2026MidIsoF (D := D) (a := a) (eA := eA)).hom.hom i
        ≫ (S2004MidComparison f g D).hom.hom i
        ≫ (S2026MidIsoG (D := D) (b := b) (eB := eB)).inv.hom i := by
  have h := congrArg (fun (m : (Pseudofunctor.toDescentData C.source.fiber
      (fun (i : R.arrows.category) => i.obj.hom)).obj
        ((f.map.app (U S)).toFunctor.obj a) ⟶
      (Pseudofunctor.toDescentData C.source.fiber
      (fun (i : R.arrows.category) => i.obj.hom)).obj
        ((g.map.app (U S)).toFunctor.obj b)) => m.hom i)
    (S2026PsiIso_map (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)
  rw [S2026PsiIso_map_app] at h
  simpa only [S2026Theta, Iso.trans_hom, Iso.symm_hom, Pseudofunctor.DescentData.comp_hom]
    using h

theorem S2026ComponentSquare (hR : R ∈ J S) (i : R.arrows.category) :
    (f.map.app (U i.obj.left)).toFunctor.map (eA.hom.hom i) ≫ (D.obj i).obj.hom
      = (((sitePseudofunctor f g).map (i.obj.hom.op.toLoc)).toFunctor.obj
            (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)).obj.hom
          ≫ (g.map.app (U i.obj.left)).toFunctor.map (eB.hom.hom i) := by
  have hSCL : (S1864SiteComparisonLeft f (i.obj.hom.op.toLoc)).hom.app a
      ≫ ((Cat.Hom.toNatIso (f.map.naturality (i.obj.hom.op.toLoc))).symm.app a).hom = 𝟙 _ :=
    Iso.hom_inv_id_app (Cat.Hom.toNatIso (f.map.naturality (i.obj.hom.op.toLoc))) a
  have h1 : (S1864SiteComparisonLeft f (i.obj.hom.op.toLoc)).hom.app a
      ≫ (S2026MidIsoF (D := D) (a := a) (eA := eA)).hom.hom i
      = (f.map.app (U i.obj.left)).toFunctor.map (eA.hom.hom i) := by
    rw [S2026MidIsoF_hom, ← Category.assoc, hSCL, Category.id_comp]
  have h1gen : ∀ {Y : C.source.fiber.obj (U i.obj.left)}
      (k : (f.map.app (U i.obj.left)).toFunctor.obj (S2004FstDescentData f g D).obj i ⟶ Y),
      (S1864SiteComparisonLeft f (i.obj.hom.op.toLoc)).hom.app a
        ≫ ((S2026MidIsoF (D := D) (a := a) (eA := eA)).hom.hom i ≫ k)
        = (f.map.app (U i.obj.left)).toFunctor.map (eA.hom.hom i) ≫ k := by
    intro Y k
    rw [← Category.assoc, h1]
  have h2 : (S2026MidIsoG (D := D) (b := b) (eB := eB)).inv.hom.hom i
      ≫ ((S1864SiteComparisonRight g (i.obj.hom.op.toLoc)).hom.app b
          ≫ (g.map.app (U i.obj.left)).toFunctor.map (eB.hom.hom i)) = 𝟙 _ := by
    rw [← S2026MidIsoG_hom]
    exact S2026InvComp (S2026MidIsoG (D := D) (b := b) (eB := eB)) i
  rw [S2026X_objHom, S2026PsiIso_map_eq, S2026MidComparison_hom]
  simp only [Category.assoc]
  rw [h1gen, h2]
  simp only [Category.comp_id]

noncomputable def S2026Component (hR : R ∈ J S) (i : R.arrows.category) :
    ((Pseudofunctor.toDescentData (sitePseudofunctor f g)
      (fun (i : R.arrows.category) => i.obj.hom)).obj
        (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)).obj i ≅ D.obj i :=
  ObjectProperty.isoMk
    (P := fun Y : Comma (f.map.app (U i.obj.left)).toFunctor (g.map.app (U i.obj.left)).toFunctor =>
      IsIso Y.hom)
    (X := ((Pseudofunctor.toDescentData (sitePseudofunctor f g)
      (fun (i : R.arrows.category) => i.obj.hom)).obj
        (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)).obj i)
    (Y := D.obj i)
    (Comma.isoMk (S2026CompIso eA i) (S2026CompIso eB i)
      (S2026ComponentSquare (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR i))

end Core
end LeanFormal.IUT.XiFPaper.S2026Probe