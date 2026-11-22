/-
# S2026: the reassembly of the iso-comma object -- effectivity of the iso-comma stack

S1956 reduced the stack condition for the iso-comma site pseudofunctor of the two actual
finite-etale cover maps f : A -> C and g : B -> C to the prestack half (proved in S1998)
and the effective-descent half

  S1956IsoCommaEffectivity f g
    = forall (S) (R : Sieve S), R in J S ->
        ((sitePseudofunctor f g).toDescentData (fun i => i.obj.hom)).EssSurj.

S2004 isolated the three steps (a), (b), (c) of the object-level 2-limit interchange:
(a) the middle comparison S2004MidF D ~ S2004MidG D (proved in S2004 as
S2004MidComparison);
(b) the comparison of the pushed-forward C-descent data with C.toDescentData, stated in
S2004 as S2004ComparisonStatement (proved in S2021 as S2021ComparisonStatement, from the
two general statements (G1) S2021PushComparison and (G2) S2021PushFunctorialityIso);
(c) the reassembly, i.e. the construction of the iso-comma object X = (a, b, psi) from
the resulting isomorphism of C-descent data, together with the isomorphism
(sitePseudofunctor f g).toDescentData X ~ D.

This file carries out (c), hence proves the target.

## What is proved in this file

Given a covering sieve R, an iso-comma descent datum D, effective A- and B-descent data
(a, eA) and (b, eB) (which exist because A.source and B.source are stacks), the two
C-side comparisons

  S2026MidIsoF : C.toDescentData (f_* a) ~ S2004MidF D,
  S2026MidIsoG : C.toDescentData (g_* b) ~ S2004MidG D

are the explicit composites of (G1) and (G2), so their components are known:
at an index i, S2026MidIsoF has component (f-comparison)^{-1} ; f_*(eA i), and
S2026MidIsoG has component (g-comparison) ; g_*(eB i).  Composing with the middle
comparison S2004MidComparison D gives S2026Theta, and full faithfulness of the C-side
comparison (the C-stack is a prestack) produces

  S2026PsiIso : f_* a ~ g_* b      (the iso of the comma structure morphism),

hence the iso-comma object S2026X at S.  The component at i of the required iso of
iso-comma descent data is the pair (eA i, eB i) of descent components; the compatibility
square of the comma category is S2026ComponentSquare, whose proof is the single
computation

  (f-comparison) ; [(f-comparison)^{-1} ; f_*(eA i) ; D_i ; (g-comparison ; g_*(eB i))^{-1}]
      ; (g-comparison) ; g_*(eB i)  =  f_*(eA i) ; D_i,

i.e. the cancellation of the two site comparisons (Iso.hom_inv_id_app) with the
componentwise inverse law of an isomorphism of descent data (S2026InvComp).

The comm field of the resulting isomorphism of iso-comma descent data is checked
componentwise against S2004MidComparison: by joint faithfulness of the two iso-comma
projections (S1836IsoComma_hom_ext) it suffices to check the two projections, where it
reduces to the comm fields of eA and eB respectively (S2026FstHom_ofObj, S2026SndHom_ofObj
identify the projection of the canonical descent datum of S2026X with the canonical
descent data of a and of b).

## Consumers

  S2026IsoCommaEffectivity : S1956IsoCommaEffectivity f g    (unconditional)
  S2026IsoCommaStack       : S1956IsoCommaStack f g          (via S1998IsoCommaStack_of_effectivity)
  S2026EffectivityAll      : S2004EffectivityAll

No sorry, no axiom, no Shrink/ULift/PUnit, no change of target.  The only axioms used are
propext, Classical.choice and Quot.sound; see the audit at the end.
-/
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

namespace LeanFormal.IUT.XiFPaper.S2026EffectivityReassemblyActual

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

abbrev U (S : Site) : LocallyDiscrete Siteᵒᵖ :=
  LocallyDiscrete.mk (Opposite.op S)

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

/-! ## 1. Components of isomorphisms of descent data -/

/-- The component at an index of an isomorphism of descent data, as an isomorphism. -/
noncomputable def S2026CompIso {F : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
    {D₁ D₂ : F.DescentData (fun (i : R.arrows.category) => i.obj.hom)} (e : D₁ ≅ D₂)
    (i : R.arrows.category) : D₁.obj i ≅ D₂.obj i where
  hom := e.hom.hom i
  inv := e.inv.hom i
  hom_inv_id := by
    rw [← Pseudofunctor.DescentData.comp_hom, e.hom_inv_id, Pseudofunctor.DescentData.id_hom]
  inv_hom_id := by
    rw [← Pseudofunctor.DescentData.comp_hom, e.inv_hom_id, Pseudofunctor.DescentData.id_hom]

/-- The componentwise inverse law for an isomorphism of descent data. -/
theorem S2026InvComp {F : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
    {D₁ D₂ : F.DescentData (fun (i : R.arrows.category) => i.obj.hom)} (e : D₁ ≅ D₂)
    (i : R.arrows.category) : e.inv.hom i ≫ e.hom.hom i = 𝟙 _ := by
  have h := congrArg (fun (m : D₂ ⟶ D₂) => m.hom i) e.inv_hom_id
  rwa [Pseudofunctor.DescentData.comp_hom, Pseudofunctor.DescentData.id_hom] at h

/-! ## 2. The two C-side comparisons, explicitly -/

/-- The f-side comparison of C-descent data, as the explicit composite of the general
comparison (G1) with the functoriality (G2) applied to eA. -/
noncomputable def S2026MidIsoF :
    (Pseudofunctor.toDescentData C.source.fiber (fun (i : R.arrows.category) => i.obj.hom)).obj
        ((f.map.app (U S)).toFunctor.obj a) ≅ S2004MidF f g D :=
  S2021PushComparison (R := R) f.map a ≪≫ S2021PushFunctorialityIso (R := R) f.map eA

/-- The g-side comparison of C-descent data. -/
noncomputable def S2026MidIsoG :
    (Pseudofunctor.toDescentData C.source.fiber (fun (i : R.arrows.category) => i.obj.hom)).obj
        ((g.map.app (U S)).toFunctor.obj b) ≅ S2004MidG f g D :=
  S2021PushComparison (R := R) g.map b ≪≫ S2021PushFunctorialityIso (R := R) g.map eB

/-- The composite comparison through the middle comparison. -/
noncomputable def S2026Theta :
    (Pseudofunctor.toDescentData C.source.fiber (fun (i : R.arrows.category) => i.obj.hom)).obj
        ((f.map.app (U S)).toFunctor.obj a) ≅
      (Pseudofunctor.toDescentData C.source.fiber (fun (i : R.arrows.category) => i.obj.hom)).obj
        ((g.map.app (U S)).toFunctor.obj b) :=
  S2026MidIsoF (D := D) (a := a) (eA := eA) ≪≫ S2004MidComparison f g D
    ≪≫ (S2026MidIsoG (D := D) (b := b) (eB := eB)).symm

/-- The component formula for the f-side comparison. -/
theorem S2026MidIsoF_hom (i : R.arrows.category) :
    (S2026MidIsoF (D := D) (a := a) (eA := eA)).hom.hom i =
      ((Cat.Hom.toNatIso (f.map.naturality (i.obj.hom.op.toLoc))).symm.app a).hom
        ≫ (f.map.app (U i.obj.left)).toFunctor.map (eA.hom.hom i) := by
  rfl

/-- The component formula for the g-side comparison. -/
theorem S2026MidIsoG_hom (i : R.arrows.category) :
    (S2026MidIsoG (D := D) (b := b) (eB := eB)).hom.hom i =
      (S1864SiteComparisonRight g (i.obj.hom.op.toLoc)).hom.app b
        ≫ (g.map.app (U i.obj.left)).toFunctor.map (eB.hom.hom i) := by
  rfl

/-- The component formula for the middle comparison. -/
theorem S2026MidComparison_hom (i : R.arrows.category) :
    (S2004MidComparison f g D).hom.hom i = (D.obj i).obj.hom := by
  rfl

/-! ## 3. Full faithfulness of the C-side comparison and the iso-comma object -/

/-- Full faithfulness of the C-side comparison for a covering sieve (the C-stack is a
prestack). -/
noncomputable def S2026CFF (hR : R ∈ J S) :
    (Pseudofunctor.toDescentData C.source.fiber
      (fun (i : R.arrows.category) => i.obj.hom)).FullyFaithful :=
  letI := C.source.isStack.toIsPrestack
  (C.source.fiber.isPrestackFor' R hR).fullyFaithful

/-- The isomorphism in the C-fibre between the two comma structure objects, produced by
full faithfulness from S2026Theta. -/
noncomputable def S2026PsiIso (hR : R ∈ J S) :
    ((f.map.app (U S)).toFunctor.obj a) ≅ ((g.map.app (U S)).toFunctor.obj b) :=
  (S2026CFF (C := C) (R := R) hR).preimageIso
    (S2026Theta (D := D) (a := a) (eA := eA) (b := b) (eB := eB))

/-- **The reassembled iso-comma object** at the base test object. -/
noncomputable def S2026X (hR : R ∈ J S) : (sitePseudofunctor f g).obj (U S) :=
  ⟨Comma.mk a b (S2026PsiIso (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).hom,
    (S2026PsiIso (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).isIso_hom⟩

/-- The defining property of the isomorphism S2026PsiIso: its image under the C-side
comparison is S2026Theta. -/
theorem S2026PsiIso_map (hR : R ∈ J S) :
    (Pseudofunctor.toDescentData C.source.fiber
      (fun (i : R.arrows.category) => i.obj.hom)).map
        (S2026PsiIso (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).hom
      = (S2026Theta (D := D) (a := a) (eA := eA) (b := b) (eB := eB)).hom :=
  (S2026CFF (C := C) (R := R) hR).map_preimage _

/-- The two projections of the reassembled object. -/
theorem S2026X_obj_left (hR : R ∈ J S) :
    (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).obj.left = a := rfl

theorem S2026X_obj_right (hR : R ∈ J S) :
    (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).obj.right = b := rfl

theorem S2026X_obj_hom (hR : R ∈ J S) :
    (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).obj.hom
      = (S2026PsiIso (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).hom := rfl

/-- The structure morphism of a restricted reassembled object: S1998ObjHom. -/
theorem S2026X_objHom (hR : R ∈ J S) (i : R.arrows.category) :
    (((sitePseudofunctor f g).map (i.obj.hom.op.toLoc)).toFunctor.obj
        (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)).obj.hom
      = (S1864SiteComparisonLeft f (i.obj.hom.op.toLoc)).hom.app
            (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).obj.left
        ≫ (C.source.fiber.map (i.obj.hom.op.toLoc)).toFunctor.map
            (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).obj.hom
        ≫ (S1864SiteComparisonRight g (i.obj.hom.op.toLoc)).hom.app
            (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).obj.right := by
  have h := S1998ObjHom f g (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)
    (Opposite.op (Over.mk i.obj.hom))
  simpa only [Opposite.unop_op, Over.mk_left, Over.mk_hom] using h

/-- The structure morphism of a restricted reassembled object, in terms of the two
effective descent data and the comma structure isomorphism. -/
theorem S2026X_objHom' (hR : R ∈ J S) (i : R.arrows.category) :
    (((sitePseudofunctor f g).map (i.obj.hom.op.toLoc)).toFunctor.obj
        (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)).obj.hom
      = (S1864SiteComparisonLeft f (i.obj.hom.op.toLoc)).hom.app a
        ≫ (C.source.fiber.map (i.obj.hom.op.toLoc)).toFunctor.map
            (S2026PsiIso (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).hom
        ≫ (S1864SiteComparisonRight g (i.obj.hom.op.toLoc)).hom.app b :=
  S2026X_objHom (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR i

/-- The component of the C-side comparison of S2026PsiIso, read at an index. -/
theorem S2026PsiIso_map_app (hR : R ∈ J S) (i : R.arrows.category) :
    ((Pseudofunctor.toDescentData C.source.fiber
      (fun (i : R.arrows.category) => i.obj.hom)).map
        (S2026PsiIso (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).hom).hom i
      = (C.source.fiber.map (i.obj.hom.op.toLoc)).toFunctor.map
        (S2026PsiIso (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).hom := rfl

/-- The component of S2026PsiIso, expanded through the two comparisons and the middle
comparison. -/
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

/-! ## 4. The explicit hom field of the canonical descent data -/

/-- The hom component of the canonical descent datum of the reassembled object. -/
theorem S2026ToDescentData_hom_app (hR : R ∈ J S) {Y : Site} (q : Y ⟶ S)
    (i₁ i₂ : R.arrows.category) (f₁ : Y ⟶ i₁.obj.left) (f₂ : Y ⟶ i₂.obj.left)
    (hf₁ : f₁ ≫ i₁.obj.hom = q) (hf₂ : f₂ ≫ i₂.obj.hom = q) :
    (((Pseudofunctor.toDescentData (sitePseudofunctor f g)
        (fun (i : R.arrows.category) => i.obj.hom)).obj
          (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)).hom
        q f₁ f₂ hf₁ hf₂)
      = ((sitePseudofunctor f g).mapComp' i₁.obj.hom.op.toLoc f₁.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₁])).inv.toNatTrans.app
              (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)
        ≫ ((sitePseudofunctor f g).mapComp' i₂.obj.hom.op.toLoc f₂.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₂])).hom.toNatTrans.app
              (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR) := rfl

/-- The hom component of the canonical descent datum of the effective A-descent datum. -/
theorem S2026AToDescentData_hom_app {Y : Site} (q : Y ⟶ S)
    (i₁ i₂ : R.arrows.category) (f₁ : Y ⟶ i₁.obj.left) (f₂ : Y ⟶ i₂.obj.left)
    (hf₁ : f₁ ≫ i₁.obj.hom = q) (hf₂ : f₂ ≫ i₂.obj.hom = q) :
    (((Pseudofunctor.toDescentData A.source.fiber
        (fun (i : R.arrows.category) => i.obj.hom)).obj a).hom q f₁ f₂ hf₁ hf₂)
      = (A.source.fiber.mapComp' i₁.obj.hom.op.toLoc f₁.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₁])).inv.toNatTrans.app a
        ≫ (A.source.fiber.mapComp' i₂.obj.hom.op.toLoc f₂.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₂])).hom.toNatTrans.app a := rfl

/-- The hom component of the canonical descent datum of the effective B-descent datum. -/
theorem S2026BToDescentData_hom_app {Y : Site} (q : Y ⟶ S)
    (i₁ i₂ : R.arrows.category) (f₁ : Y ⟶ i₁.obj.left) (f₂ : Y ⟶ i₂.obj.left)
    (hf₁ : f₁ ≫ i₁.obj.hom = q) (hf₂ : f₂ ≫ i₂.obj.hom = q) :
    (((Pseudofunctor.toDescentData B.source.fiber
        (fun (i : R.arrows.category) => i.obj.hom)).obj b).hom q f₁ f₂ hf₁ hf₂)
      = (B.source.fiber.mapComp' i₁.obj.hom.op.toLoc f₁.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₁])).inv.toNatTrans.app b
        ≫ (B.source.fiber.mapComp' i₂.obj.hom.op.toLoc f₂.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₂])).hom.toNatTrans.app b := rfl

/-- The first projection of the structure morphism of the extracted A-descent datum. -/
theorem S2026FstDHom {Y : Site} (q : Y ⟶ S) (i₁ i₂ : R.arrows.category)
    (f₁ : Y ⟶ i₁.obj.left) (f₂ : Y ⟶ i₂.obj.left)
    (hf₁ : f₁ ≫ i₁.obj.hom = q) (hf₂ : f₂ ≫ i₂.obj.hom = q) :
    (S1836IsoCommaFst (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
        (D.hom q f₁ f₂ hf₁ hf₂) = (S2004FstDescentData f g D).hom q f₁ f₂ hf₁ hf₂ := rfl

/-- The second projection of the structure morphism of the extracted B-descent datum. -/
theorem S2026SndDHom {Y : Site} (q : Y ⟶ S) (i₁ i₂ : R.arrows.category)
    (f₁ : Y ⟶ i₁.obj.left) (f₂ : Y ⟶ i₂.obj.left)
    (hf₁ : f₁ ≫ i₁.obj.hom = q) (hf₂ : f₂ ≫ i₂.obj.hom = q) :
    (S1836IsoCommaSnd (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
        (D.hom q f₁ f₂ hf₁ hf₂) = (S2004SndDescentData f g D).hom q f₁ f₂ hf₁ hf₂ := rfl

/-- The first projection of the canonical descent datum of the reassembled object is the
canonical descent datum of the effective A-descent datum. -/
theorem S2026FstHom_ofObj (hR : R ∈ J S) {Y : Site} (q : Y ⟶ S)
    (i₁ i₂ : R.arrows.category) (f₁ : Y ⟶ i₁.obj.left) (f₂ : Y ⟶ i₂.obj.left)
    (hf₁ : f₁ ≫ i₁.obj.hom = q) (hf₂ : f₂ ≫ i₂.obj.hom = q) :
    (S1836IsoCommaFst (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
        (((Pseudofunctor.toDescentData (sitePseudofunctor f g)
          (fun (i : R.arrows.category) => i.obj.hom)).obj
            (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)).hom q f₁ f₂ hf₁ hf₂)
      = ((Pseudofunctor.toDescentData A.source.fiber
          (fun (i : R.arrows.category) => i.obj.hom)).obj a).hom q f₁ f₂ hf₁ hf₂ := by
  have h0 : (S1836IsoCommaFst (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
        (((Pseudofunctor.toDescentData (sitePseudofunctor f g)
          (fun (i : R.arrows.category) => i.obj.hom)).obj
            (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)).hom q f₁ f₂ hf₁ hf₂)
      = (S1836IsoCommaFst (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
        (((sitePseudofunctor f g).mapComp' i₁.obj.hom.op.toLoc f₁.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₁])).inv.toNatTrans.app
              (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)
          ≫ ((sitePseudofunctor f g).mapComp' i₂.obj.hom.op.toLoc f₂.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₂])).hom.toNatTrans.app
              (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)) :=
    congrArg _ (S2026ToDescentData_hom_app (D := D) (a := a) (eA := eA) (b := b) (eB := eB)
      hR q i₁ i₂ f₁ f₂ hf₁ hf₂)
  have h1 : (S1836IsoCommaFst (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
        (((sitePseudofunctor f g).mapComp' i₁.obj.hom.op.toLoc f₁.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₁])).inv.toNatTrans.app
              (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)
          ≫ ((sitePseudofunctor f g).mapComp' i₂.obj.hom.op.toLoc f₂.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₂])).hom.toNatTrans.app
              (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR))
      = (S1836IsoCommaFst (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
          (((sitePseudofunctor f g).mapComp' i₁.obj.hom.op.toLoc f₁.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₁])).inv.toNatTrans.app
              (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR))
        ≫ (S1836IsoCommaFst (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
          (((sitePseudofunctor f g).mapComp' i₂.obj.hom.op.toLoc f₂.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₂])).hom.toNatTrans.app
              (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)) :=
    Functor.map_comp _ _ _
  have h2 : (S1836IsoCommaFst (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
          (((sitePseudofunctor f g).mapComp' i₁.obj.hom.op.toLoc f₁.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₁])).inv.toNatTrans.app
              (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR))
      = (A.source.fiber.mapComp' i₁.obj.hom.op.toLoc f₁.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₁])).inv.toNatTrans.app
          (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).obj.left :=
    S1956Fst_mapComp'_inv f g _ _ _ _ _
  have h3 : (S1836IsoCommaFst (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
          (((sitePseudofunctor f g).mapComp' i₂.obj.hom.op.toLoc f₂.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₂])).hom.toNatTrans.app
              (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR))
      = (A.source.fiber.mapComp' i₂.obj.hom.op.toLoc f₂.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₂])).hom.toNatTrans.app
          (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).obj.left :=
    S1956Fst_mapComp' f g _ _ _ _ _
  have e1 := congrArg (fun m =>
    m ≫ (S1836IsoCommaFst (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
          (((sitePseudofunctor f g).mapComp' i₂.obj.hom.op.toLoc f₂.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₂])).hom.toNatTrans.app
              (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR))) h2
  have e2 := congrArg (fun m =>
    (A.source.fiber.mapComp' i₁.obj.hom.op.toLoc f₁.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₁])).inv.toNatTrans.app
          (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).obj.left ≫ m) h3
  have e3 : (A.source.fiber.mapComp' i₁.obj.hom.op.toLoc f₁.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₁])).inv.toNatTrans.app
          (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).obj.left
        ≫ (A.source.fiber.mapComp' i₂.obj.hom.op.toLoc f₂.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₂])).hom.toNatTrans.app
          (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).obj.left
      = ((Pseudofunctor.toDescentData A.source.fiber
          (fun (i : R.arrows.category) => i.obj.hom)).obj
            (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).obj.left).hom
          q f₁ f₂ hf₁ hf₂ := by
    rw [← S2026AToDescentData_hom_app]
  exact h0.trans (h1.trans (e1.trans (e2.trans e3)))

/-- The second projection of the canonical descent datum of the reassembled object is the
canonical descent datum of the effective B-descent datum. -/
theorem S2026SndHom_ofObj (hR : R ∈ J S) {Y : Site} (q : Y ⟶ S)
    (i₁ i₂ : R.arrows.category) (f₁ : Y ⟶ i₁.obj.left) (f₂ : Y ⟶ i₂.obj.left)
    (hf₁ : f₁ ≫ i₁.obj.hom = q) (hf₂ : f₂ ≫ i₂.obj.hom = q) :
    (S1836IsoCommaSnd (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
        (((Pseudofunctor.toDescentData (sitePseudofunctor f g)
          (fun (i : R.arrows.category) => i.obj.hom)).obj
            (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)).hom q f₁ f₂ hf₁ hf₂)
      = ((Pseudofunctor.toDescentData B.source.fiber
          (fun (i : R.arrows.category) => i.obj.hom)).obj b).hom q f₁ f₂ hf₁ hf₂ := by
  have h0 : (S1836IsoCommaSnd (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
        (((Pseudofunctor.toDescentData (sitePseudofunctor f g)
          (fun (i : R.arrows.category) => i.obj.hom)).obj
            (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)).hom q f₁ f₂ hf₁ hf₂)
      = (S1836IsoCommaSnd (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
        (((sitePseudofunctor f g).mapComp' i₁.obj.hom.op.toLoc f₁.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₁])).inv.toNatTrans.app
              (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)
          ≫ ((sitePseudofunctor f g).mapComp' i₂.obj.hom.op.toLoc f₂.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₂])).hom.toNatTrans.app
              (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)) :=
    congrArg _ (S2026ToDescentData_hom_app (D := D) (a := a) (eA := eA) (b := b) (eB := eB)
      hR q i₁ i₂ f₁ f₂ hf₁ hf₂)
  have h1 : (S1836IsoCommaSnd (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
        (((sitePseudofunctor f g).mapComp' i₁.obj.hom.op.toLoc f₁.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₁])).inv.toNatTrans.app
              (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)
          ≫ ((sitePseudofunctor f g).mapComp' i₂.obj.hom.op.toLoc f₂.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₂])).hom.toNatTrans.app
              (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR))
      = (S1836IsoCommaSnd (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
          (((sitePseudofunctor f g).mapComp' i₁.obj.hom.op.toLoc f₁.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₁])).inv.toNatTrans.app
              (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR))
        ≫ (S1836IsoCommaSnd (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
          (((sitePseudofunctor f g).mapComp' i₂.obj.hom.op.toLoc f₂.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₂])).hom.toNatTrans.app
              (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)) :=
    Functor.map_comp _ _ _
  have h2 : (S1836IsoCommaSnd (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
          (((sitePseudofunctor f g).mapComp' i₁.obj.hom.op.toLoc f₁.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₁])).inv.toNatTrans.app
              (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR))
      = (B.source.fiber.mapComp' i₁.obj.hom.op.toLoc f₁.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₁])).inv.toNatTrans.app
          (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).obj.right :=
    S1956Snd_mapComp'_inv f g _ _ _ _ _
  have h3 : (S1836IsoCommaSnd (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
          (((sitePseudofunctor f g).mapComp' i₂.obj.hom.op.toLoc f₂.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₂])).hom.toNatTrans.app
              (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR))
      = (B.source.fiber.mapComp' i₂.obj.hom.op.toLoc f₂.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₂])).hom.toNatTrans.app
          (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).obj.right :=
    S1956Snd_mapComp' f g _ _ _ _ _
  have e1 := congrArg (fun m =>
    m ≫ (S1836IsoCommaSnd (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
          (((sitePseudofunctor f g).mapComp' i₂.obj.hom.op.toLoc f₂.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₂])).hom.toNatTrans.app
              (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR))) h2
  have e2 := congrArg (fun m =>
    (B.source.fiber.mapComp' i₁.obj.hom.op.toLoc f₁.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₁])).inv.toNatTrans.app
          (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).obj.right ≫ m) h3
  have e3 : (B.source.fiber.mapComp' i₁.obj.hom.op.toLoc f₁.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₁])).inv.toNatTrans.app
          (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).obj.right
        ≫ (B.source.fiber.mapComp' i₂.obj.hom.op.toLoc f₂.op.toLoc q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₂])).hom.toNatTrans.app
          (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).obj.right
      = ((Pseudofunctor.toDescentData B.source.fiber
          (fun (i : R.arrows.category) => i.obj.hom)).obj
            (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR).obj.right).hom
          q f₁ f₂ hf₁ hf₂ := by
    rw [← S2026BToDescentData_hom_app]
  exact h0.trans (h1.trans (e1.trans (e2.trans e3)))

/-! ## 5. The compatibility square of the component isomorphism -/

/-- The cancellation of the f-side site comparison against the inverse naturality
comparison of the strong transformation f.map. -/
theorem S2026FComparison_cancel (i : R.arrows.category) :
    (S1864SiteComparisonLeft f (i.obj.hom.op.toLoc)).hom.app a
      ≫ ((Cat.Hom.toNatIso (f.map.naturality (i.obj.hom.op.toLoc))).symm.app a).hom = 𝟙 _ :=
  Iso.hom_inv_id_app (Cat.Hom.toNatIso (f.map.naturality (i.obj.hom.op.toLoc))) a

/-- **The compatibility square** of the component of the reassembled isomorphism of
iso-comma descent data at the index i. -/
theorem S2026ComponentSquare (hR : R ∈ J S) (i : R.arrows.category) :
    (f.map.app (U i.obj.left)).toFunctor.map (eA.hom.hom i) ≫ (D.obj i).obj.hom
      = (((sitePseudofunctor f g).map (i.obj.hom.op.toLoc)).toFunctor.obj
            (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)).obj.hom
          ≫ (g.map.app (U i.obj.left)).toFunctor.map (eB.hom.hom i) := by
  have hSCL := S2026FComparison_cancel (f := f) (a := a) (R := R) i
  have h1 : (S1864SiteComparisonLeft f (i.obj.hom.op.toLoc)).hom.app a
      ≫ (S2026MidIsoF (D := D) (a := a) (eA := eA)).hom.hom i
      = (f.map.app (U i.obj.left)).toFunctor.map (eA.hom.hom i) := by
    rw [S2026MidIsoF_hom, ← Category.assoc, hSCL, Category.id_comp]
  have h1gen : ∀ {Y : C.source.fiber.obj (U i.obj.left)}
      (k : (f.map.app (U i.obj.left)).toFunctor.obj ((S2004FstDescentData f g D).obj i) ⟶ Y),
      (S1864SiteComparisonLeft f (i.obj.hom.op.toLoc)).hom.app a
        ≫ ((S2026MidIsoF (D := D) (a := a) (eA := eA)).hom.hom i ≫ k)
        = (f.map.app (U i.obj.left)).toFunctor.map (eA.hom.hom i) ≫ k := by
    intro Y k
    rw [← Category.assoc, h1]
  have h2 : (S2026MidIsoG (D := D) (b := b) (eB := eB)).inv.hom i
      ≫ ((S1864SiteComparisonRight g (i.obj.hom.op.toLoc)).hom.app b
          ≫ (g.map.app (U i.obj.left)).toFunctor.map (eB.hom.hom i)) = 𝟙 _ := by
    rw [← S2026MidIsoG_hom]
    exact S2026InvComp (S2026MidIsoG (D := D) (b := b) (eB := eB)) i
  rw [S2026X_objHom', S2026PsiIso_map_eq, S2026MidComparison_hom]
  simp only [Category.assoc]
  rw [h1gen, h2]
  simp only [Category.comp_id]

/-- **The component of the reassembled isomorphism of iso-comma descent data** at the
index i. -/
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

/-- The first projection of the component. -/
theorem S2026Component_fst (hR : R ∈ J S) (i : R.arrows.category) :
    (S1836IsoCommaFst (f.map.app (U i.obj.left)).toFunctor
      (g.map.app (U i.obj.left)).toFunctor).map
        (S2026Component (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR i).hom
      = eA.hom.hom i := rfl

/-- The second projection of the component. -/
theorem S2026Component_snd (hR : R ∈ J S) (i : R.arrows.category) :
    (S1836IsoCommaSnd (f.map.app (U i.obj.left)).toFunctor
      (g.map.app (U i.obj.left)).toFunctor).map
        (S2026Component (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR i).hom
      = eB.hom.hom i := rfl

/-! ## 6. The reassembled isomorphism of iso-comma descent data -/

/-- **The reassembly**: the canonical descent datum of the reassembled iso-comma object
S2026X is isomorphic to the given iso-comma descent datum D. -/
noncomputable def S2026DescentIso (hR : R ∈ J S) :
    (Pseudofunctor.toDescentData (sitePseudofunctor f g)
      (fun (i : R.arrows.category) => i.obj.hom)).obj
        (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR) ≅ D :=
  Pseudofunctor.DescentData.isoMk
    (fun i => S2026Component (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR i)
    (by
      intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
      apply S1836IsoComma_hom_ext (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor
      · simp only [Functor.map_comp]
        have hL1 := S1956Fst_map f g (f₁.op.toLoc)
          (S2026Component (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR i₁).hom
        have hL2 : (A.source.fiber.map f₁.op.toLoc).toFunctor.map
              ((S1836IsoCommaFst (f.map.app (U i₁.obj.left)).toFunctor
                (g.map.app (U i₁.obj.left)).toFunctor).map
                  (S2026Component (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR i₁).hom)
            = (A.source.fiber.map f₁.op.toLoc).toFunctor.map (eA.hom.hom i₁) :=
          congrArg (fun m => (A.source.fiber.map f₁.op.toLoc).toFunctor.map m)
            (S2026Component_fst (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR i₁)
        have hL3 := S2026FstDHom (f := f) (g := g) (D := D) q i₁ i₂ f₁ f₂ hf₁ hf₂
        have hR1 := S2026FstHom_ofObj (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR
          q i₁ i₂ f₁ f₂ hf₁ hf₂
        have hR2 : (S1836IsoCommaFst (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
              (((sitePseudofunctor f g).map f₂.op.toLoc).toFunctor.map
                (S2026Component (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR i₂).hom)
            = (A.source.fiber.map f₂.op.toLoc).toFunctor.map (eA.hom.hom i₂) :=
          (S1956Fst_map f g (f₂.op.toLoc)
            (S2026Component (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR i₂).hom).trans
            (congrArg (fun m => (A.source.fiber.map f₂.op.toLoc).toFunctor.map m)
              (S2026Component_fst (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR i₂))
        have hL : (S1836IsoCommaFst (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
              (((sitePseudofunctor f g).map f₁.op.toLoc).toFunctor.map
                (S2026Component (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR i₁).hom)
            ≫ (S1836IsoCommaFst (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
              (D.hom q f₁ f₂ hf₁ hf₂)
          = (A.source.fiber.map f₁.op.toLoc).toFunctor.map (eA.hom.hom i₁)
            ≫ (S2004FstDescentData f g D).hom q f₁ f₂ hf₁ hf₂ :=
          (congrArg (fun m => m ≫ (S1836IsoCommaFst (f.map.app (U Y)).toFunctor
              (g.map.app (U Y)).toFunctor).map (D.hom q f₁ f₂ hf₁ hf₂)) hL1).trans
            ((congrArg (fun m => m ≫ (S1836IsoCommaFst (f.map.app (U Y)).toFunctor
              (g.map.app (U Y)).toFunctor).map (D.hom q f₁ f₂ hf₁ hf₂)) hL2).trans
              (congrArg (fun m => (A.source.fiber.map f₁.op.toLoc).toFunctor.map (eA.hom.hom i₁)
                ≫ m) hL3))
        have hR : (S1836IsoCommaFst (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
              (((Pseudofunctor.toDescentData (sitePseudofunctor f g)
                (fun (i : R.arrows.category) => i.obj.hom)).obj
                  (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)).hom
                  q f₁ f₂ hf₁ hf₂)
            ≫ (S1836IsoCommaFst (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
              (((sitePseudofunctor f g).map f₂.op.toLoc).toFunctor.map
                (S2026Component (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR i₂).hom)
          = ((Pseudofunctor.toDescentData A.source.fiber
                (fun (i : R.arrows.category) => i.obj.hom)).obj a).hom q f₁ f₂ hf₁ hf₂
            ≫ (A.source.fiber.map f₂.op.toLoc).toFunctor.map (eA.hom.hom i₂) :=
          (congrArg (fun m => m ≫ (S1836IsoCommaFst (f.map.app (U Y)).toFunctor
              (g.map.app (U Y)).toFunctor).map
                (((sitePseudofunctor f g).map f₂.op.toLoc).toFunctor.map
                  (S2026Component (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR i₂).hom)) hR1).trans
            (congrArg (fun m => ((Pseudofunctor.toDescentData A.source.fiber
                (fun (i : R.arrows.category) => i.obj.hom)).obj a).hom q f₁ f₂ hf₁ hf₂ ≫ m) hR2)
        exact hL.trans ((eA.hom.comm q f₁ f₂ hf₁ hf₂).trans hR.symm)
      · simp only [Functor.map_comp]
        have hL1 := S1956Snd_map f g (f₁.op.toLoc)
          (S2026Component (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR i₁).hom
        have hL2 : (B.source.fiber.map f₁.op.toLoc).toFunctor.map
              ((S1836IsoCommaSnd (f.map.app (U i₁.obj.left)).toFunctor
                (g.map.app (U i₁.obj.left)).toFunctor).map
                  (S2026Component (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR i₁).hom)
            = (B.source.fiber.map f₁.op.toLoc).toFunctor.map (eB.hom.hom i₁) :=
          congrArg (fun m => (B.source.fiber.map f₁.op.toLoc).toFunctor.map m)
            (S2026Component_snd (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR i₁)
        have hL3 := S2026SndDHom (f := f) (g := g) (D := D) q i₁ i₂ f₁ f₂ hf₁ hf₂
        have hR1 := S2026SndHom_ofObj (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR
          q i₁ i₂ f₁ f₂ hf₁ hf₂
        have hR2 : (S1836IsoCommaSnd (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
              (((sitePseudofunctor f g).map f₂.op.toLoc).toFunctor.map
                (S2026Component (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR i₂).hom)
            = (B.source.fiber.map f₂.op.toLoc).toFunctor.map (eB.hom.hom i₂) :=
          (S1956Snd_map f g (f₂.op.toLoc)
            (S2026Component (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR i₂).hom).trans
            (congrArg (fun m => (B.source.fiber.map f₂.op.toLoc).toFunctor.map m)
              (S2026Component_snd (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR i₂))
        have hL : (S1836IsoCommaSnd (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
              (((sitePseudofunctor f g).map f₁.op.toLoc).toFunctor.map
                (S2026Component (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR i₁).hom)
            ≫ (S1836IsoCommaSnd (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
              (D.hom q f₁ f₂ hf₁ hf₂)
          = (B.source.fiber.map f₁.op.toLoc).toFunctor.map (eB.hom.hom i₁)
            ≫ (S2004SndDescentData f g D).hom q f₁ f₂ hf₁ hf₂ :=
          (congrArg (fun m => m ≫ (S1836IsoCommaSnd (f.map.app (U Y)).toFunctor
              (g.map.app (U Y)).toFunctor).map (D.hom q f₁ f₂ hf₁ hf₂)) hL1).trans
            ((congrArg (fun m => m ≫ (S1836IsoCommaSnd (f.map.app (U Y)).toFunctor
              (g.map.app (U Y)).toFunctor).map (D.hom q f₁ f₂ hf₁ hf₂)) hL2).trans
              (congrArg (fun m => (B.source.fiber.map f₁.op.toLoc).toFunctor.map (eB.hom.hom i₁)
                ≫ m) hL3))
        have hR : (S1836IsoCommaSnd (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
              (((Pseudofunctor.toDescentData (sitePseudofunctor f g)
                (fun (i : R.arrows.category) => i.obj.hom)).obj
                  (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)).hom
                  q f₁ f₂ hf₁ hf₂)
            ≫ (S1836IsoCommaSnd (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
              (((sitePseudofunctor f g).map f₂.op.toLoc).toFunctor.map
                (S2026Component (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR i₂).hom)
          = ((Pseudofunctor.toDescentData B.source.fiber
                (fun (i : R.arrows.category) => i.obj.hom)).obj b).hom q f₁ f₂ hf₁ hf₂
            ≫ (B.source.fiber.map f₂.op.toLoc).toFunctor.map (eB.hom.hom i₂) :=
          (congrArg (fun m => m ≫ (S1836IsoCommaSnd (f.map.app (U Y)).toFunctor
              (g.map.app (U Y)).toFunctor).map
                (((sitePseudofunctor f g).map f₂.op.toLoc).toFunctor.map
                  (S2026Component (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR i₂).hom)) hR1).trans
            (congrArg (fun m => ((Pseudofunctor.toDescentData B.source.fiber
                (fun (i : R.arrows.category) => i.obj.hom)).obj b).hom q f₁ f₂ hf₁ hf₂ ≫ m) hR2)
        exact hL.trans ((eB.hom.comm q f₁ f₂ hf₁ hf₂).trans hR.symm))

end Core

/-! ## 7. The effectivity half and the stack condition -/

section Assembly

/-- **The effective-descent half of the iso-comma stack**, unconditionally: for every
covering sieve the comparison functor of the iso-comma pseudofunctor is essentially
surjective. -/
theorem S2026IsoCommaEffectivity {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C) :
    S1956IsoCommaEffectivity f g := by
  intro S R hR
  refine ⟨fun D => ?_⟩
  have hA := A.source.isStack.essSurj_of_sieve R hR
  have hB := B.source.isStack.essSurj_of_sieve R hR
  obtain ⟨a, ⟨eA⟩⟩ := hA.mem_essImage (S2004FstDescentData f g D)
  obtain ⟨b, ⟨eB⟩⟩ := hB.mem_essImage (S2004SndDescentData f g D)
  exact ⟨S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR,
    ⟨S2026DescentIso (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR⟩⟩

/-- **The stack condition for the actual iso-comma pseudofunctor** (S1864 (b)). -/
theorem S2026IsoCommaStack {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C) :
    S1956IsoCommaStack f g :=
  S1998IsoCommaStack_of_effectivity f g (S2026IsoCommaEffectivity f g)

/-- The uniform form: effectivity for every cospan of actual finite-etale cover maps. -/
theorem S2026EffectivityAll : S2004EffectivityAll :=
  fun {A B C} f g => S2026IsoCommaEffectivity f g

end Assembly

/-! ## 8. Checks and axiom audit -/

#check S2026CompIso
#check S2026InvComp
#check S2026MidIsoF
#check S2026MidIsoG
#check S2026Theta
#check S2026MidIsoF_hom
#check S2026MidIsoG_hom
#check S2026MidComparison_hom
#check S2026CFF
#check S2026PsiIso
#check S2026X
#check S2026PsiIso_map
#check S2026X_objHom
#check S2026PsiIso_map_eq
#check S2026ToDescentData_hom_app
#check S2026AToDescentData_hom_app
#check S2026BToDescentData_hom_app
#check S2026FstDHom
#check S2026SndDHom
#check S2026FstHom_ofObj
#check S2026SndHom_ofObj
#check S2026FComparison_cancel
#check S2026ComponentSquare
#check S2026Component
#check S2026Component_fst
#check S2026Component_snd
#check S2026DescentIso
#check S2026IsoCommaEffectivity
#check S2026IsoCommaStack
#check S2026EffectivityAll
#check @S1956IsoCommaEffectivity
#check @S1956IsoCommaStack
#check @S2004EffectivityAll

#print axioms S2026InvComp
#print axioms S2026CFF
#print axioms S2026PsiIso_map
#print axioms S2026ToDescentData_hom_app
#print axioms S2026FstHom_ofObj
#print axioms S2026SndHom_ofObj
#print axioms S2026ComponentSquare
#print axioms S2026Component_fst
#print axioms S2026Component_snd
#print axioms S2026DescentIso
#print axioms S2026IsoCommaEffectivity
#print axioms S2026IsoCommaStack
#print axioms S2026EffectivityAll

end LeanFormal.IUT.XiFPaper.S2026EffectivityReassemblyActual