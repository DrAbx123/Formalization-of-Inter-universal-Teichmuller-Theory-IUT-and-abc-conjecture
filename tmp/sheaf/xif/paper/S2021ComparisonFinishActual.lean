import tmp.sheaf.xif.paper.S2012EffectivityComparisonActual

/-!
# S2021: the general push-forward comparison and the S2004 comparison statement

S2012 reduced the effectivity half of the iso-comma stack to two general statements:
(G1) S2012PushToDescentDataStatement and (G2) S2012PushFunctorialityStatement.  This
file proves both, hence S2004ComparisonStatement, and records the next exact missing
(the reassembly of the iso-comma object, i.e. the effectivity statement itself).

## What is proved in this file

1. S2021PushCommCore: the comm field of (G1), i.e. the compatibility of the candidate
   components with the two hom fields.  This is the identity that S2012 isolated as its
   single open proof obligation; it is proved from the two primed pasting identities
   S2012natCompInvApp_comp' and S2012natCompHomApp_comp', using the unit laws in the
   form Iso.hom_inv_id_assoc / Iso.inv_hom_id_assoc with explicit trailing factors.
   This avoids ever transporting a 𝟙 between the two object forms (Cat vs
   Bundled.Category), which is the transparency issue recorded in S2012.
2. S2021PushComparison: the general comparison (G1) as an isomorphism of descent data.
3. S2021PushToDescentData: the statement (G1).
4. S2021PushFunctorialityIso / S2021PushFunctoriality: the statement (G2).
5. S2021ComparisonStatement: S2004ComparisonStatement, obtained from (G1) and (G2) by
   the reduction S2012Comparison_of_statements.

## Honest boundary

The reassembly step (c) of S2004 -- from S2004ComparisonStatement to the effectivity
statement S1956IsoCommaEffectivity f g -- is not formalized here; see the final section
for the exact shape of what remains.  No sorry, no axiom, no change of target.  The only
axioms used are propext, Classical.choice and Quot.sound; see the audit at the end.
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

namespace LeanFormal.IUT.XiFPaper.S2021ComparisonFinishActual

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

universe u

abbrev K := S1726K
abbrev Site := SchemeOverField K

abbrev U (S : Site) : LocallyDiscrete Siteᵒᵖ :=
  LocallyDiscrete.mk (Opposite.op S)

/-! ## 1. The comm field of the general comparison -/
/-- **The comm field of the general comparison, in components.**  This is the single
componentwise identity that was the open obligation of S2012: the compatibility of the
candidate components (the inverse naturality comparisons of the strong transformation
`α`) with the two `hom` fields of the pushed-forward and of the canonical descent data.
It is proved from the two primed pasting identities of S2012
(`S2012natCompInvApp_comp'`, `S2012natCompHomApp_comp'`) together with the unit laws of
the comparison isomorphisms, packaged as `Iso.hom_inv_id_assoc` and
`Iso.inv_hom_id_assoc` with explicit trailing factors, so that no `𝟙` has to be
transported between the `Cat` and the `Bundled.Category` object forms. -/
theorem S2021PushCommCore
    {F G : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
    (α : Pseudofunctor.StrongTrans F G) {S : Site} {R : Sieve S} (M : F.obj (U S))
    {Y : Site} (q : Y ⟶ S) {i₁ i₂ : R.arrows.category}
    (f₁ : Y ⟶ i₁.obj.left) (f₂ : Y ⟶ i₂.obj.left)
    (hf₁ : f₁ ≫ i₁.obj.hom = q) (hf₂ : f₂ ≫ i₂.obj.hom = q)
    (p₁ : i₁.obj.hom.op.toLoc ≫ f₁.op.toLoc = q.op.toLoc)
    (p₂ : i₂.obj.hom.op.toLoc ≫ f₂.op.toLoc = q.op.toLoc) :
    (G.map f₁.op.toLoc).toFunctor.map ((α.naturality (i₁.obj.hom.op.toLoc)).inv.toNatTrans.app M) ≫
      (α.naturality f₁.op.toLoc).inv.toNatTrans.app ((F.map (i₁.obj.hom.op.toLoc)).toFunctor.obj M) ≫
        (α.app (U Y)).toFunctor.map (((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app M) ≫ ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M)) ≫
          (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) =
      (((G.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ ((G.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app ((α.app (U S)).toFunctor.obj M))) ≫
        (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).inv.toNatTrans.app M) := by
  have h₁ := S2012natCompInvApp_comp' (F := F) (G := G) (α := α)
    (φ := i₁.obj.hom.op.toLoc) (ψ := f₁.op.toLoc) (χ := q.op.toLoc) p₁ (x := M)
  have h₂ := S2012natCompHomApp_comp' (F := F) (G := G) (α := α)
    (φ := i₂.obj.hom.op.toLoc) (ψ := f₂.op.toLoc) (χ := q.op.toLoc) p₂ (x := M)
  have hGC1 : ((G.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ ((G.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).hom.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) = 𝟙 _ := by
    rw [← Cat.Hom₂.comp_app, (G.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv_hom_id, Cat.Hom₂.id_app]
  have hA1P1 : (G.map f₁.op.toLoc).toFunctor.map ((α.naturality (i₁.obj.hom.op.toLoc)).inv.toNatTrans.app M) ≫ (α.naturality f₁.op.toLoc).inv.toNatTrans.app ((F.map (i₁.obj.hom.op.toLoc)).toFunctor.obj M) = ((G.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (α.naturality q.op.toLoc).inv.toNatTrans.app M ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).hom.toNatTrans.app M) := by
    rw [← h₁, ← Category.assoc, hGC1, Category.id_comp]
  have hA1P1p : (G.map f₁.op.toLoc).toFunctor.map ((α.naturality (i₁.obj.hom.op.toLoc)).inv.toNatTrans.app M) ≫ (α.naturality f₁.op.toLoc).inv.toNatTrans.app ((F.map (i₁.obj.hom.op.toLoc)).toFunctor.obj M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) =
      ((G.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (α.naturality q.op.toLoc).inv.toNatTrans.app M ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).hom.toNatTrans.app M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) := by
    simpa only [Category.assoc] using congrArg (fun m => m ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M)) hA1P1
  have hpF1 : (α.app (U Y)).toFunctor.map ((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).hom.toNatTrans.app M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) = (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) :=
    Iso.hom_inv_id_assoc ((α.app (U Y)).toFunctor.mapIso ((Cat.Hom.toNatIso (F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁)).app M)) ((α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M))
  have h2a : ((G.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (α.naturality q.op.toLoc).inv.toNatTrans.app M ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).hom.toNatTrans.app M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) =
      ((G.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (α.naturality q.op.toLoc).inv.toNatTrans.app M ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) := by
    simpa only [Category.assoc] using congrArg (fun m => ((G.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (α.naturality q.op.toLoc).inv.toNatTrans.app M ≫ m) hpF1
  have hGmBA : (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).hom.toNatTrans.app M) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).inv.toNatTrans.app M) = 𝟙 _ := Iso.hom_inv_id ((G.map f₂.op.toLoc).toFunctor.mapIso ((Cat.Hom.toNatIso (α.naturality (i₂.obj.hom.op.toLoc))).app M))
  have hZinvZhom : (α.naturality q.op.toLoc).inv.toNatTrans.app M ≫ (α.naturality q.op.toLoc).hom.toNatTrans.app M = 𝟙 _ := Iso.inv_hom_id ((Cat.Hom.toNatIso (α.naturality q.op.toLoc)).app M)
  have hZ2 : (α.naturality q.op.toLoc).inv.toNatTrans.app M ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) = ((G.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).inv.toNatTrans.app M) := by
    have h1' : (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) = (α.naturality q.op.toLoc).hom.toNatTrans.app M ≫ ((G.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).inv.toNatTrans.app M) := by
      calc (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M)
          = (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) ≫ ((G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).hom.toNatTrans.app M) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).inv.toNatTrans.app M)) := by erw [hGmBA, Category.comp_id]
        _ = ((α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).hom.toNatTrans.app M)) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).inv.toNatTrans.app M) := by simp only [Category.assoc]
        _ = ((α.naturality q.op.toLoc).hom.toNatTrans.app M ≫ ((G.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app ((α.app (U S)).toFunctor.obj M))) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).inv.toNatTrans.app M) := by rw [← h₂]
        _ = (α.naturality q.op.toLoc).hom.toNatTrans.app M ≫ ((G.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).inv.toNatTrans.app M) := by simp only [Category.assoc]
    calc (α.naturality q.op.toLoc).inv.toNatTrans.app M ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M)
        = (α.naturality q.op.toLoc).inv.toNatTrans.app M ≫ ((α.naturality q.op.toLoc).hom.toNatTrans.app M ≫ ((G.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).inv.toNatTrans.app M)) := by rw [h1']
      _ = ((α.naturality q.op.toLoc).inv.toNatTrans.app M ≫ (α.naturality q.op.toLoc).hom.toNatTrans.app M) ≫ ((G.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).inv.toNatTrans.app M) := by simp only [Category.assoc]
      _ = ((G.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).inv.toNatTrans.app M) := by rw [hZinvZhom, Category.id_comp]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  calc (G.map f₁.op.toLoc).toFunctor.map ((α.naturality (i₁.obj.hom.op.toLoc)).inv.toNatTrans.app M) ≫ (α.naturality f₁.op.toLoc).inv.toNatTrans.app ((F.map (i₁.obj.hom.op.toLoc)).toFunctor.obj M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M)
      = ((G.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (α.naturality q.op.toLoc).inv.toNatTrans.app M ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).hom.toNatTrans.app M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) := hA1P1p
    _ = ((G.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (α.naturality q.op.toLoc).inv.toNatTrans.app M ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) := h2a
    _ = ((G.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (((G.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).inv.toNatTrans.app M)) := by rw [hZ2]

/-! ## 2. The general comparison (G1) -/

/-- The general comparison: the pushed-forward canonical descent datum of M along the
strong transformation alpha is isomorphic, as G-descent data, to the canonical descent
datum of (alpha.app (U S)).obj M.  The components are the inverse naturality
comparisons ((Cat.Hom.toNatIso (alpha.naturality _)).symm.app M), and its comm field is
S2021PushCommCore. -/
noncomputable def S2021PushComparison
    {F G : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
    (α : Pseudofunctor.StrongTrans F G) {S : Site} {R : Sieve S} (M : F.obj (U S)) :
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
      rw [S2012toNatIso_symm_app_hom, S2012toNatIso_symm_app_hom]
      exact S2021PushCommCore α M q f₁ f₂ hf₁ hf₂ _ _)

/-- Statement (G1), proved. -/
theorem S2021PushToDescentData : S2012PushToDescentDataStatement := by
  intro F G α S R M
  exact ⟨S2021PushComparison (R := R) α M⟩

/-! ## 3. Functoriality (G2) -/

/-- **Functoriality of the push-forward**, in components: a morphism (indeed an
isomorphism) of F-descent data is sent to an isomorphism of the pushed-forward
G-descent data.  The components are the images under alpha.app of the components of e
(S2012PushComponent); the comm field is the naturality of the comparison isomorphisms of
alpha at the components of e, together with the comm field of e. -/
noncomputable def S2021PushFunctorialityIso
    {F G : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
    (α : Pseudofunctor.StrongTrans F G) {S : Site} {R : Sieve S}
    {D₁ D₂ : F.DescentData (fun (i : R.arrows.category) => i.obj.hom)} (e : D₁ ≅ D₂) :
    S2004PushDescentData (R := R) α D₁ ≅ S2004PushDescentData (R := R) α D₂ :=
  Pseudofunctor.DescentData.isoMk (fun i => S2012PushComponent (R := R) α e i) (by
  intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
  simp only [S2004PushDescentData, S2012PushComponent_hom]
  have hcomm := e.hom.comm q f₁ f₂ hf₁ hf₂
  have hnat₁ : (G.map f₁.op.toLoc).toFunctor.map
        ((α.app (U (Rfam R i₁))).toFunctor.map (e.hom.hom i₁)) ≫
        (α.naturality f₁.op.toLoc).inv.toNatTrans.app (D₂.obj i₁) =
      (α.naturality f₁.op.toLoc).inv.toNatTrans.app (D₁.obj i₁) ≫
        (α.app (U Y)).toFunctor.map ((F.map f₁.op.toLoc).toFunctor.map (e.hom.hom i₁)) := by
    simpa only [Cat.Hom.comp_map, Cat.Hom.comp_obj] using
      (α.naturality f₁.op.toLoc).inv.toNatTrans.naturality (e.hom.hom i₁)
  have hnat₂ : (α.app (U Y)).toFunctor.map ((F.map f₂.op.toLoc).toFunctor.map (e.hom.hom i₂)) ≫
        (α.naturality f₂.op.toLoc).hom.toNatTrans.app (D₂.obj i₂) =
      (α.naturality f₂.op.toLoc).hom.toNatTrans.app (D₁.obj i₂) ≫
        (G.map f₂.op.toLoc).toFunctor.map ((α.app (U (Rfam R i₂))).toFunctor.map (e.hom.hom i₂)) := by
    simpa only [Cat.Hom.comp_map, Cat.Hom.comp_obj] using
      (α.naturality f₂.op.toLoc).hom.toNatTrans.naturality (e.hom.hom i₂)
  have hmap₁ : (α.app (U Y)).toFunctor.map ((F.map f₁.op.toLoc).toFunctor.map (e.hom.hom i₁)) ≫ (α.app (U Y)).toFunctor.map (D₂.hom q f₁ f₂ hf₁ hf₂) =
      (α.app (U Y)).toFunctor.map (D₁.hom q f₁ f₂ hf₁ hf₂) ≫ (α.app (U Y)).toFunctor.map ((F.map f₂.op.toLoc).toFunctor.map (e.hom.hom i₂)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hcomm]
  have step1 : (G.map f₁.op.toLoc).toFunctor.map ((α.app (U (Rfam R i₁))).toFunctor.map (e.hom.hom i₁)) ≫ (α.naturality f₁.op.toLoc).inv.toNatTrans.app (D₂.obj i₁) ≫ ((α.app (U Y)).toFunctor.map (D₂.hom q f₁ f₂ hf₁ hf₂) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app (D₂.obj i₂)) =
      (α.naturality f₁.op.toLoc).inv.toNatTrans.app (D₁.obj i₁) ≫ (α.app (U Y)).toFunctor.map ((F.map f₁.op.toLoc).toFunctor.map (e.hom.hom i₁)) ≫ ((α.app (U Y)).toFunctor.map (D₂.hom q f₁ f₂ hf₁ hf₂) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app (D₂.obj i₂)) := by
    simpa only [Category.assoc] using
      congrArg (fun m => m ≫ ((α.app (U Y)).toFunctor.map (D₂.hom q f₁ f₂ hf₁ hf₂) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app (D₂.obj i₂))) hnat₁
  have step2 : (α.naturality f₁.op.toLoc).inv.toNatTrans.app (D₁.obj i₁) ≫ (α.app (U Y)).toFunctor.map ((F.map f₁.op.toLoc).toFunctor.map (e.hom.hom i₁)) ≫ (α.app (U Y)).toFunctor.map (D₂.hom q f₁ f₂ hf₁ hf₂) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app (D₂.obj i₂) =
      (α.naturality f₁.op.toLoc).inv.toNatTrans.app (D₁.obj i₁) ≫ (α.app (U Y)).toFunctor.map (D₁.hom q f₁ f₂ hf₁ hf₂) ≫ (α.app (U Y)).toFunctor.map ((F.map f₂.op.toLoc).toFunctor.map (e.hom.hom i₂)) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app (D₂.obj i₂) := by
    simpa only [Category.assoc] using
      congrArg (fun m => (α.naturality f₁.op.toLoc).inv.toNatTrans.app (D₁.obj i₁) ≫ m ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app (D₂.obj i₂)) hmap₁
  have step3 : (α.naturality f₁.op.toLoc).inv.toNatTrans.app (D₁.obj i₁) ≫ (α.app (U Y)).toFunctor.map (D₁.hom q f₁ f₂ hf₁ hf₂) ≫ (α.app (U Y)).toFunctor.map ((F.map f₂.op.toLoc).toFunctor.map (e.hom.hom i₂)) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app (D₂.obj i₂) =
      ((α.naturality f₁.op.toLoc).inv.toNatTrans.app (D₁.obj i₁) ≫ (α.app (U Y)).toFunctor.map (D₁.hom q f₁ f₂ hf₁ hf₂) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app (D₁.obj i₂)) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.app (U (Rfam R i₂))).toFunctor.map (e.hom.hom i₂)) := by
    rw [hnat₂]
    simp only [Category.assoc]
  calc (G.map f₁.op.toLoc).toFunctor.map ((α.app (U (Rfam R i₁))).toFunctor.map (e.hom.hom i₁)) ≫ (α.naturality f₁.op.toLoc).inv.toNatTrans.app (D₂.obj i₁) ≫ (α.app (U Y)).toFunctor.map (D₂.hom q f₁ f₂ hf₁ hf₂) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app (D₂.obj i₂)
      = (α.naturality f₁.op.toLoc).inv.toNatTrans.app (D₁.obj i₁) ≫ (α.app (U Y)).toFunctor.map ((F.map f₁.op.toLoc).toFunctor.map (e.hom.hom i₁)) ≫ (α.app (U Y)).toFunctor.map (D₂.hom q f₁ f₂ hf₁ hf₂) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app (D₂.obj i₂) := step1
    _ = (α.naturality f₁.op.toLoc).inv.toNatTrans.app (D₁.obj i₁) ≫ (α.app (U Y)).toFunctor.map (D₁.hom q f₁ f₂ hf₁ hf₂) ≫ (α.app (U Y)).toFunctor.map ((F.map f₂.op.toLoc).toFunctor.map (e.hom.hom i₂)) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app (D₂.obj i₂) := step2
    _ = ((α.naturality f₁.op.toLoc).inv.toNatTrans.app (D₁.obj i₁) ≫ (α.app (U Y)).toFunctor.map (D₁.hom q f₁ f₂ hf₁ hf₂) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app (D₁.obj i₂)) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.app (U (Rfam R i₂))).toFunctor.map (e.hom.hom i₂)) := step3)

/-- Statement (G2), proved: functoriality of the push-forward of descent data. -/
theorem S2021PushFunctoriality : S2012PushFunctorialityStatement := by
  intro F G α S R D₁ D₂ e
  exact ⟨S2021PushFunctorialityIso α e⟩

/-! ## 4. The S2004 comparison statement -/

/-- The S2004 comparison statement (statement (b) of S2004), proved from (G1) and (G2)
by the reduction of S2012. -/
theorem S2021ComparisonStatement : S2004ComparisonStatement :=
  S2012Comparison_of_statements S2021PushToDescentData S2021PushFunctoriality


/-! ## 5. Checks and axiom audit -/

#check S2021PushCommCore
#check S2021PushComparison
#check S2021PushToDescentData
#check S2021PushFunctorialityIso
#check S2021PushFunctoriality
#check S2021ComparisonStatement
#check @S2012Comparison_of_statements
#check @S2004ComparisonStatement
#check @S2012PushToDescentDataStatement
#check @S2012PushFunctorialityStatement

#print axioms S2021PushCommCore
#print axioms S2021PushComparison
#print axioms S2021PushToDescentData
#print axioms S2021PushFunctorialityIso
#print axioms S2021PushFunctoriality
#print axioms S2021ComparisonStatement

/-! ## 6. The next exact missing: the reassembly of the iso-comma object

The comparison statement S2004ComparisonStatement is now proved.  The next step of
S2004's plan -- step (c), the reassembly -- is NOT formalized in this file.  Concretely,
S1956IsoCommaEffectivity f g asks for essential surjectivity of

  (sitePseudofunctor f g).toDescentData (fun i => i.obj.hom)

for every covering sieve, i.e. for every iso-comma descent datum D an object X of the
iso-comma over the base S together with an isomorphism
(sitePseudofunctor f g).toDescentData X  ≅  D.  The pieces that are now available are:

* the A-side and B-side extraction S2004FstDescentData f g D and S2004SndDescentData f g D
  (S2004);
* the effectivity of the three fibres: the fields A.source.isStack, B.source.isStack,
  C.source.isStack of the covers (EtaleStackOverField.isStack) give both the essential
  surjectivity and the prestack (full faithfulness) conditions of the corresponding
  toDescentData functors for every covering sieve;
* the comparison (G1) S2021PushComparison and the functoriality (G2)
  S2021PushFunctorialityIso of this file, which produce an isomorphism
  C.toDescentData ((f.map.app (U S)).obj A)  ≅  S2004MidF f g D
  from an effective A-descent datum for S2004FstDescentData f g D, and the analogous
  g-side comparison;
* the middle comparison S2004MidComparison f g D : S2004MidF f g D  ≅  S2004MidG f g D
  (S2004).

What is missing is the last step: producing the iso-comma object X from the resulting
isomorphism (f.map.app (U S)).obj A  ≅  (g.map.app (U S)).obj B in C.obj (U S)
(obtained by full faithfulness of C.toDescentData), and then the isomorphism of descent
data (sitePseudofunctor f g).toDescentData X  ≅  D whose comm field is checked
componentwise against S2004MidComparison.  This is the exact first missing for the
effectivity target S1956IsoCommaEffectivity f g.
-/

end LeanFormal.IUT.XiFPaper.S2021ComparisonFinishActual
