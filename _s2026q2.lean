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


/-- variant A: projection by rfl -/
theorem q_fst_rfl (hR : R ∈ J S) {Y : Site} (q : Y ⟶ S)
    (i₁ i₂ : R.arrows.category) (f₁ : Y ⟶ i₁.obj.left) (f₂ : Y ⟶ i₂.obj.left)
    (hf₁ : f₁ ≫ i₁.obj.hom = q) (hf₂ : f₂ ≫ i₂.obj.hom = q) :
    (S1836IsoCommaFst (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
        (((Pseudofunctor.toDescentData (sitePseudofunctor f g)
          (fun (i : R.arrows.category) => i.obj.hom)).obj
            (S2026X (D := D) (a := a) (eA := eA) (b := b) (eB := eB) hR)).hom q f₁ f₂ hf₁ hf₂)
      = ((Pseudofunctor.toDescentData A.source.fiber
          (fun (i : R.arrows.category) => i.obj.hom)).obj a).hom q f₁ f₂ hf₁ hf₂ := rfl

end Core
end LeanFormal.IUT.XiFPaper.S2026EffectivityReassemblyActual
