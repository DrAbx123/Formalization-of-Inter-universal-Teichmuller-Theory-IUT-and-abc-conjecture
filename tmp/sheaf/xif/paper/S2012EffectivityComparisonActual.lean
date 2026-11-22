import tmp.sheaf.xif.paper.S2004IsoCommaEffectivityActual

/-!
# S2012: the comparison of the pushed-forward descent data with the C-side comparison

## Context

S2004 reduced the effectivity half `S1956IsoCommaEffectivity f g` of the iso-comma
stack to three steps:

* (a) the middle comparison `S2004MidF f g D ≅ S2004MidG f g D` -- proved in S2004;
* (b) the comparison with the `f`-side comparison: for an effective `A`-descent datum
  `a` with `(A.toDescentData _).obj a ≅ S2004FstDescentData f g D`, an isomorphism of
  `C`-descent data `(C.toDescentData _).obj ((f.map.app _).obj a) ≅ S2004MidF f g D`;
  S2004 only stated this as the `Prop` `S2004ComparisonStatement` (no inhabitant);
* (c) the `g`-side analogue and the reassembly of the iso-comma object.

## What is proved in this file

1. `S2012mapComp'_hom_app`: the component formula for the flexible restriction
   comparison `mapComp'` in terms of `mapComp` and the 2-cell adjustment.
2. `S2012natComp_nat2_hom` / `S2012natComp_nat2_inv`: the componentwise 2-naturality
   of the strong naturality comparison with respect to a 2-cell of the site.
3. `S2012natCompInvApp_comp'` / `S2012natCompHomApp_comp'`: the primed pasting
   identities -- the versions of the S1935 componentwise coherences
   `natCompHomApp_comp` / `natCompInvApp_comp` for the flexible `mapComp'`, i.e.
   exactly the coherences that the definition of `DescentData.ofObj` (which uses
   `mapComp'`) requires.  These are the technical core of the (b)-comparison.
4. The candidate comparison components
   `((Cat.Hom.toNatIso (α.naturality (i.obj.hom).op.toLoc)).symm.app M)`
   (the inverse of the S1864/S1998 comparison `S1864SiteComparisonLeft`), and the
   componentwise push comparison `S2012PushComponent`.

## Exact missing

The general comparison -- for every strong transformation `α : F ⟶ G` of
pseudofunctors on the etale site and every `M : F.obj (U S)`, an isomorphism of
`G`-descent data

  `(G.toDescentData _).obj ((α.app (U S)).obj M) ≅ S2004PushDescentData α (F.toDescentData _ M)`

whose components are the candidate ones in (4) -- is not proved here; it is
recorded as the `Prop` `S2012PushToDescentDataStatement`.  Its single proof obligation
is the compatibility of the candidate components with the two `hom` fields, i.e.
the commutativity of

  `(G.map f₁).map (e i₁).hom ≫ (G.mapComp' φ₂ f₂ q).hom = (G.mapComp' φ₁ f₁ q).inv ≫ (G.map f₂).map (e i₂).hom`

after unfolding `DescentData.ofObj`; with (2) and (3) this reduces to the
cancellation of the two restrictions `mapComp'` against the `f`-side naturality
comparisons, which is the one place where the `Cat`-versus-`Bundled Category`
transparency issue of the `𝟙`-typed unit laws has to be resolved.

Also recorded (not proved) is the functoriality of the push-forward of descent data
in the descent datum itself (`S2012PushFunctorialityStatement`).

The target `S2004ComparisonStatement` is not claimed: only the reduction
`S2012Comparison_of_statements` (both missing statements imply the target) is proved.
No `sorry`, no axiom, no change of target.  The only axioms used are
`propext`, `Classical.choice` and `Quot.sound`; see the audit at the end.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2012EffectivityComparisonActual

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

universe u

abbrev K := S1726K
abbrev Site := SchemeOverField K

abbrev U (S : Site) : LocallyDiscrete Siteᵒᵖ :=
  LocallyDiscrete.mk (Opposite.op S)
theorem S2012mapComp'_hom_app
    {F : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
    {A₀ B₀ C₀ : LocallyDiscrete Siteᵒᵖ} (φ : A₀ ⟶ B₀) (ψ : B₀ ⟶ C₀) (χ : A₀ ⟶ C₀)
    (h : φ ≫ ψ = χ) (y : ↑(F.obj A₀)) :
    (F.mapComp' φ ψ χ h).hom.toNatTrans.app y =
      (F.map₂ (eqToHom (by rw [h] : χ = φ ≫ ψ))).toNatTrans.app y ≫
        (F.mapComp φ ψ).hom.toNatTrans.app y := rfl

theorem S2012natComp_nat2_hom
    {F G : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
    (α : Pseudofunctor.StrongTrans F G)
    {A₀ B₀ : LocallyDiscrete Siteᵒᵖ} {f g : A₀ ⟶ B₀} (η : f ⟶ g) (x : ↑(F.obj A₀)) :
    (α.app B₀).toFunctor.map ((F.map₂ η).toNatTrans.app x) ≫
        (α.naturality g).hom.toNatTrans.app x =
      (α.naturality f).hom.toNatTrans.app x ≫
        (G.map₂ η).toNatTrans.app ((α.app A₀).toFunctor.obj x) := by
  have h := α.naturality_naturality η
  have h' := congrArg (fun (φ : (F.map f ≫ α.app B₀) ⟶ (α.app A₀ ≫ G.map g)) =>
    φ.toNatTrans.app x) h
  simpa only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerRight_app,
    CategoryTheory.Cat.whiskerLeft_app] using h'

theorem S2012natComp_nat2_inv
    {F G : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
    (α : Pseudofunctor.StrongTrans F G)
    {A₀ B₀ : LocallyDiscrete Siteᵒᵖ} {f g : A₀ ⟶ B₀} (η : f ⟶ g) (x : ↑(F.obj A₀)) :
    (G.map₂ η).toNatTrans.app ((α.app A₀).toFunctor.obj x) ≫
        (α.naturality g).inv.toNatTrans.app x =
      (α.naturality f).inv.toNatTrans.app x ≫
        (α.app B₀).toFunctor.map ((F.map₂ η).toNatTrans.app x) := by
  have h2 := S2012natComp_nat2_hom (F := F) (G := G) α η x
  have hcf : (α.naturality f).inv.toNatTrans.app x ≫
      (α.naturality f).hom.toNatTrans.app x = 𝟙 _ := by
    rw [← CategoryTheory.Cat.Hom₂.comp_app, (α.naturality f).inv_hom_id,
      CategoryTheory.Cat.Hom₂.id_app]
  have hcg : (α.naturality g).hom.toNatTrans.app x ≫
      (α.naturality g).inv.toNatTrans.app x = 𝟙 _ := by
    rw [← CategoryTheory.Cat.Hom₂.comp_app, (α.naturality g).hom_inv_id,
      CategoryTheory.Cat.Hom₂.id_app]
  have h5 : (α.naturality f).inv.toNatTrans.app x ≫
      ((α.app B₀).toFunctor.map ((F.map₂ η).toNatTrans.app x) ≫
        (α.naturality g).hom.toNatTrans.app x) =
      (G.map₂ η).toNatTrans.app ((α.app A₀).toFunctor.obj x) := by
    rw [h2]
    rw [← Category.assoc, hcf]
    simp
  calc (G.map₂ η).toNatTrans.app ((α.app A₀).toFunctor.obj x) ≫
        (α.naturality g).inv.toNatTrans.app x
      = ((α.naturality f).inv.toNatTrans.app x ≫
          ((α.app B₀).toFunctor.map ((F.map₂ η).toNatTrans.app x) ≫
            (α.naturality g).hom.toNatTrans.app x)) ≫ (α.naturality g).inv.toNatTrans.app x := by
        rw [h5]
    _ = (α.naturality f).inv.toNatTrans.app x ≫
          (α.app B₀).toFunctor.map ((F.map₂ η).toNatTrans.app x) := by
        rw [Category.assoc, Category.assoc, hcg]
        simp

theorem S2012natCompInvApp_comp'
    {F G : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
    (α : Pseudofunctor.StrongTrans F G)
    {A₀ B₀ C₀ : LocallyDiscrete Siteᵒᵖ} (φ : A₀ ⟶ B₀) (ψ : B₀ ⟶ C₀) (χ : A₀ ⟶ C₀)
    (h : φ ≫ ψ = χ) (x : ↑(F.obj A₀)) :
    (G.mapComp' φ ψ χ h).hom.toNatTrans.app ((α.app A₀).toFunctor.obj x) ≫
        (G.map ψ).toFunctor.map ((α.naturality φ).inv.toNatTrans.app x) ≫
          (α.naturality ψ).inv.toNatTrans.app ((F.map φ).toFunctor.obj x) =
      (α.naturality χ).inv.toNatTrans.app x ≫
        (α.app C₀).toFunctor.map ((F.mapComp' φ ψ χ h).hom.toNatTrans.app x) := by
  have hc := natCompInvApp_comp (F := F) (G := G) α φ ψ x
  have hn := S2012natComp_nat2_inv (F := F) (G := G) α
    (f := χ) (g := φ ≫ ψ) (eqToHom (by rw [h] : χ = φ ≫ ψ)) x
  calc (G.mapComp' φ ψ χ h).hom.toNatTrans.app ((α.app A₀).toFunctor.obj x) ≫
        (G.map ψ).toFunctor.map ((α.naturality φ).inv.toNatTrans.app x) ≫
          (α.naturality ψ).inv.toNatTrans.app ((F.map φ).toFunctor.obj x)
      = ((G.map₂ (eqToHom (by rw [h] : χ = φ ≫ ψ))).toNatTrans.app
            ((α.app A₀).toFunctor.obj x) ≫
          (G.mapComp φ ψ).hom.toNatTrans.app ((α.app A₀).toFunctor.obj x)) ≫
        ((G.map ψ).toFunctor.map ((α.naturality φ).inv.toNatTrans.app x) ≫
          (α.naturality ψ).inv.toNatTrans.app ((F.map φ).toFunctor.obj x)) := by
        rw [S2012mapComp'_hom_app (F := G) φ ψ χ h]
    _ = (G.map₂ (eqToHom (by rw [h] : χ = φ ≫ ψ))).toNatTrans.app
            ((α.app A₀).toFunctor.obj x) ≫
          ((G.mapComp φ ψ).hom.toNatTrans.app ((α.app A₀).toFunctor.obj x) ≫
            ((G.map ψ).toFunctor.map ((α.naturality φ).inv.toNatTrans.app x) ≫
              (α.naturality ψ).inv.toNatTrans.app ((F.map φ).toFunctor.obj x))) := by
        rw [Category.assoc]
    _ = (G.map₂ (eqToHom (by rw [h] : χ = φ ≫ ψ))).toNatTrans.app
            ((α.app A₀).toFunctor.obj x) ≫
          ((α.naturality (φ ≫ ψ)).inv.toNatTrans.app x ≫
            (α.app C₀).toFunctor.map ((F.mapComp φ ψ).hom.toNatTrans.app x)) := by
        rw [hc]
    _ = ((G.map₂ (eqToHom (by rw [h] : χ = φ ≫ ψ))).toNatTrans.app
            ((α.app A₀).toFunctor.obj x) ≫
          (α.naturality (φ ≫ ψ)).inv.toNatTrans.app x) ≫
            (α.app C₀).toFunctor.map ((F.mapComp φ ψ).hom.toNatTrans.app x) := by
        rw [Category.assoc]
    _ = ((α.naturality χ).inv.toNatTrans.app x ≫
          (α.app C₀).toFunctor.map
            ((F.map₂ (eqToHom (by rw [h] : χ = φ ≫ ψ))).toNatTrans.app x)) ≫
            (α.app C₀).toFunctor.map ((F.mapComp φ ψ).hom.toNatTrans.app x) := by
        rw [hn]
    _ = (α.naturality χ).inv.toNatTrans.app x ≫
          ((α.app C₀).toFunctor.map
            ((F.map₂ (eqToHom (by rw [h] : χ = φ ≫ ψ))).toNatTrans.app x) ≫
            (α.app C₀).toFunctor.map ((F.mapComp φ ψ).hom.toNatTrans.app x)) := by
        rw [Category.assoc]
    _ = (α.naturality χ).inv.toNatTrans.app x ≫
          (α.app C₀).toFunctor.map
            ((F.map₂ (eqToHom (by rw [h] : χ = φ ≫ ψ))).toNatTrans.app x ≫
              (F.mapComp φ ψ).hom.toNatTrans.app x) := by
        rw [← Functor.map_comp]
    _ = (α.naturality χ).inv.toNatTrans.app x ≫
          (α.app C₀).toFunctor.map ((F.mapComp' φ ψ χ h).hom.toNatTrans.app x) := by
        rw [S2012mapComp'_hom_app (F := F) φ ψ χ h]

theorem S2012natCompHomApp_comp'
    {F G : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
    (α : Pseudofunctor.StrongTrans F G)
    {A₀ B₀ C₀ : LocallyDiscrete Siteᵒᵖ} (φ : A₀ ⟶ B₀) (ψ : B₀ ⟶ C₀) (χ : A₀ ⟶ C₀)
    (h : φ ≫ ψ = χ) (x : ↑(F.obj A₀)) :
    (α.naturality χ).hom.toNatTrans.app x ≫
        (G.mapComp' φ ψ χ h).hom.toNatTrans.app ((α.app A₀).toFunctor.obj x) =
      (α.app C₀).toFunctor.map ((F.mapComp' φ ψ χ h).hom.toNatTrans.app x) ≫
        (α.naturality ψ).hom.toNatTrans.app ((F.map φ).toFunctor.obj x) ≫
          (G.map ψ).toFunctor.map ((α.naturality φ).hom.toNatTrans.app x) := by
  have hc := natCompHomApp_comp (F := F) (G := G) α φ ψ x
  have hn := S2012natComp_nat2_hom (F := F) (G := G) α
    (f := χ) (g := φ ≫ ψ) (eqToHom (by rw [h] : χ = φ ≫ ψ)) x
  calc (α.naturality χ).hom.toNatTrans.app x ≫
        (G.mapComp' φ ψ χ h).hom.toNatTrans.app ((α.app A₀).toFunctor.obj x)
      = (α.naturality χ).hom.toNatTrans.app x ≫
          ((G.map₂ (eqToHom (by rw [h] : χ = φ ≫ ψ))).toNatTrans.app
              ((α.app A₀).toFunctor.obj x) ≫
            (G.mapComp φ ψ).hom.toNatTrans.app ((α.app A₀).toFunctor.obj x)) := by
        rw [S2012mapComp'_hom_app (F := G) φ ψ χ h]
    _ = ((α.naturality χ).hom.toNatTrans.app x ≫
          (G.map₂ (eqToHom (by rw [h] : χ = φ ≫ ψ))).toNatTrans.app
            ((α.app A₀).toFunctor.obj x)) ≫
          (G.mapComp φ ψ).hom.toNatTrans.app ((α.app A₀).toFunctor.obj x) := by
        rw [Category.assoc]
    _ = ((α.app C₀).toFunctor.map
            ((F.map₂ (eqToHom (by rw [h] : χ = φ ≫ ψ))).toNatTrans.app x) ≫
          (α.naturality (φ ≫ ψ)).hom.toNatTrans.app x) ≫
          (G.mapComp φ ψ).hom.toNatTrans.app ((α.app A₀).toFunctor.obj x) := by
        rw [← hn]
    _ = (α.app C₀).toFunctor.map
            ((F.map₂ (eqToHom (by rw [h] : χ = φ ≫ ψ))).toNatTrans.app x) ≫
          ((α.naturality (φ ≫ ψ)).hom.toNatTrans.app x ≫
            (G.mapComp φ ψ).hom.toNatTrans.app ((α.app A₀).toFunctor.obj x)) := by
        rw [Category.assoc]
    _ = (α.app C₀).toFunctor.map
            ((F.map₂ (eqToHom (by rw [h] : χ = φ ≫ ψ))).toNatTrans.app x) ≫
          ((α.app C₀).toFunctor.map ((F.mapComp φ ψ).hom.toNatTrans.app x) ≫
            (α.naturality ψ).hom.toNatTrans.app ((F.map φ).toFunctor.obj x) ≫
              (G.map ψ).toFunctor.map ((α.naturality φ).hom.toNatTrans.app x)) := by
        rw [hc]
    _ = ((α.app C₀).toFunctor.map
            ((F.map₂ (eqToHom (by rw [h] : χ = φ ≫ ψ))).toNatTrans.app x) ≫
          (α.app C₀).toFunctor.map ((F.mapComp φ ψ).hom.toNatTrans.app x)) ≫
            (α.naturality ψ).hom.toNatTrans.app ((F.map φ).toFunctor.obj x) ≫
              (G.map ψ).toFunctor.map ((α.naturality φ).hom.toNatTrans.app x) := by
        rw [Category.assoc]
    _ = (α.app C₀).toFunctor.map
            ((F.map₂ (eqToHom (by rw [h] : χ = φ ≫ ψ))).toNatTrans.app x ≫
              (F.mapComp φ ψ).hom.toNatTrans.app x) ≫
            (α.naturality ψ).hom.toNatTrans.app ((F.map φ).toFunctor.obj x) ≫
              (G.map ψ).toFunctor.map ((α.naturality φ).hom.toNatTrans.app x) := by
        rw [← Functor.map_comp]
    _ = (α.app C₀).toFunctor.map ((F.mapComp' φ ψ χ h).hom.toNatTrans.app x) ≫
            (α.naturality ψ).hom.toNatTrans.app ((F.map φ).toFunctor.obj x) ≫
              (G.map ψ).toFunctor.map ((α.naturality φ).hom.toNatTrans.app x) := by
        rw [S2012mapComp'_hom_app (F := F) φ ψ χ h]
/-- The inverse naturality comparison, read at the object: the candidate components
of the comparison between the pushed-forward and the canonical C-descent data. -/
@[simp] lemma S2012toNatIso_symm_app_hom
    {F G : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
    (α : Pseudofunctor.StrongTrans F G)
    {S : Site} {R : Sieve S} (M : F.obj (U S)) (i : R.arrows.category) :
    ((Cat.Hom.toNatIso (α.naturality ((i.obj.hom).op.toLoc))).symm.app M).hom =
      (α.naturality ((i.obj.hom).op.toLoc)).inv.toNatTrans.app M := rfl

@[simp] lemma S2012toNatIso_symm_app_inv
    {F G : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
    (α : Pseudofunctor.StrongTrans F G)
    {S : Site} {R : Sieve S} (M : F.obj (U S)) (i : R.arrows.category) :
    ((Cat.Hom.toNatIso (α.naturality ((i.obj.hom).op.toLoc))).symm.app M).inv =
      (α.naturality ((i.obj.hom).op.toLoc)).hom.toNatTrans.app M := rfl

/-- The comparison at a single index: a morphism of descent data between D₁ and D₂
is sent by a strong transformation to a morphism between the two pushed-forward
descent data. -/
noncomputable def S2012PushComponent
    {F G : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
    (α : Pseudofunctor.StrongTrans F G)
    {S : Site} {R : Sieve S}
    {D₁ D₂ : F.DescentData (fun (i : R.arrows.category) => i.obj.hom)}
    (e : D₁ ≅ D₂) (i : R.arrows.category) :
    (S2004PushDescentData (R := R) α D₁).obj i ≅ (S2004PushDescentData (R := R) α D₂).obj i :=
  (α.app (U (Rfam R i))).toFunctor.mapIso
    { hom := e.hom.hom i
      inv := e.inv.hom i
      hom_inv_id := by
        rw [← Pseudofunctor.DescentData.comp_hom, e.hom_inv_id,
          Pseudofunctor.DescentData.id_hom]
      inv_hom_id := by
        rw [← Pseudofunctor.DescentData.comp_hom, e.inv_hom_id,
          Pseudofunctor.DescentData.id_hom] }

@[simp] lemma S2012PushComponent_hom
    {F G : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
    (α : Pseudofunctor.StrongTrans F G)
    {S : Site} {R : Sieve S}
    {D₁ D₂ : F.DescentData (fun (i : R.arrows.category) => i.obj.hom)}
    (e : D₁ ≅ D₂) (i : R.arrows.category) :
    (S2012PushComponent (R := R) α e i).hom =
      (α.app (U (Rfam R i))).toFunctor.map (e.hom.hom i) := rfl

/-- The exact first missing statement for (b'): for every strong transformation
α : F ⟶ G of pseudofunctors on the etale site and every object M of F at the test
object S, the pushed-forward canonical descent datum of M is isomorphic to the
canonical descent datum of (α.app _).obj M.  The candidate isomorphism has the
components of S2012toNatIso_symm_app_hom above; its commutativity is the one open
proof obligation. -/
def S2012PushToDescentDataStatement : Prop :=
  ∀ {F G : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
    (α : Pseudofunctor.StrongTrans F G) {S : Site} {R : Sieve S} (M : F.obj (U S)),
    Nonempty
      ((Pseudofunctor.toDescentData G (fun (i : R.arrows.category) => i.obj.hom)).obj
          ((α.app (U S)).toFunctor.obj M) ≅
        S2004PushDescentData (R := R) α
          ((Pseudofunctor.toDescentData F (fun (i : R.arrows.category) => i.obj.hom)).obj M))

/-- Functoriality of the push-forward of descent data in the descent datum: the
second open proof obligation (it only needs the functoriality of α.app and the
naturality of α.naturality, with no mapComp' involved). -/
def S2012PushFunctorialityStatement : Prop :=
  ∀ {F G : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
    (α : Pseudofunctor.StrongTrans F G) {S : Site} {R : Sieve S}
    {D₁ : F.DescentData (fun (i : R.arrows.category) => i.obj.hom)}
    {D₂ : F.DescentData (fun (i : R.arrows.category) => i.obj.hom)}
    (e : D₁ ≅ D₂),
    Nonempty (S2004PushDescentData (R := R) α D₁ ≅ S2004PushDescentData (R := R) α D₂)

/-- The reduction: the two general statements imply the S2004 missing statement
(b'). -/
theorem S2012Comparison_of_statements
    (H₁ : S2012PushToDescentDataStatement) (H₂ : S2012PushFunctorialityStatement) :
    S2004ComparisonStatement := by
  intro A B C f g S R D a h
  obtain ⟨e⟩ := h
  obtain ⟨c⟩ := @H₁ A.source.fiber C.source.fiber f.map S R a
  obtain ⟨d⟩ := @H₂ A.source.fiber C.source.fiber f.map S R _ _ e
  exact ⟨c ≪≫ d⟩

/-! ## Checks and axiom audit -/

#check S2012mapComp'_hom_app
#check S2012natComp_nat2_hom
#check S2012natComp_nat2_inv
#check S2012natCompInvApp_comp'
#check S2012natCompHomApp_comp'
#check S2012toNatIso_symm_app_hom
#check S2012PushComponent
#check S2012PushToDescentDataStatement
#check S2012PushFunctorialityStatement
#check S2012Comparison_of_statements

#print axioms S2012mapComp'_hom_app
#print axioms S2012natComp_nat2_hom
#print axioms S2012natComp_nat2_inv
#print axioms S2012natCompInvApp_comp'
#print axioms S2012natCompHomApp_comp'
#print axioms S2012toNatIso_symm_app_hom
#print axioms S2012PushComponent
#print axioms S2012PushToDescentDataStatement
#print axioms S2012PushFunctorialityStatement
#print axioms S2012Comparison_of_statements

end LeanFormal.IUT.XiFPaper.S2012EffectivityComparisonActual