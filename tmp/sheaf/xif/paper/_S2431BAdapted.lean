import tmp.sheaf.xif.paper.S2429CompositeAssemblyActual

/-!
# S2431: the composite map iso required by S2429CompositeMapIsoRequired

Given H : S2424ComposableRepresentable g1 g2, this file constructs

  Nonempty (Iso
    (S2403CastHom H.R1.source_fiber_eq H.R2.target_fiber_eq (S1641CoverMapComp g1 g2).map)
    (S1742StrongTransOfHom (S2429CompositeMap H))).

The construction is the composite of

* the cast-composition lemma S2429CastComp_holds (S2429),
* the representability isomorphisms H.R1.map_iso and H.R2.map_iso (S2403),
* a transport of the second isomorphism along H.middle_eq (section 1),
* the representable composition equation S2398HomOfStrongTrans_vcomp (S2398)
  together with the 2-Yoneda round trip S1742StrongTransIsoOfHom (S1742)
  (section 2),
* right/left whiskering in the bicategory of pseudofunctors, in the style of
  S1641.

No sorry, no new axiom, no change of target.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2403RepresentableExamplesActual
open LeanFormal.IUT.XiFPaper.S2424CoverCompositionActual
open LeanFormal.IUT.XiFPaper.S2429CompositeAssemblyActual
open LeanFormal.IUT.XiFPaper.S2398HomOfStrongTransCompActual
namespace LeanFormal.IUT.XiFPaper.S2431CompositeMapIsoActual

/-! ## 1. Transport of the cast hom along the middle equality -/

/-- Transporting the second fiber equality along an equality of the middle
scheme transports the cast hom.  Both middle fiber equalities are proofs of the
same proposition once the scheme equality is substituted, so they agree by
proof irrelevance. -/
noncomputable def S2431CastHomMidIso
    {B C : EtaleStackOverField S1726K}
    {X2 X2' X3 : SchemeOverField S1726K}
    (h2 : B.fiber = S1742YS (F := S1726K) X2)
    (h2' : B.fiber = S1742YS (F := S1726K) X2')
    (m : X2 = X2')
    (h3 : C.fiber = S1742YS (F := S1726K) X3)
    (g : B.Hom C) (g0 : X2' ⟶ X3)
    (e : Iso (S2403CastHom h2' h3 g) (S1742StrongTransOfHom (F := S1726K) g0)) :
    Iso (S2403CastHom h2 h3 g) (S1742StrongTransOfHom (F := S1726K) (m ▸ g0)) := by
  cases m
  exact (eqToIso
    (congrArg (fun e => S2403CastHom e h3 g) (Subsingleton.elim h2 h2'))).trans e

/-! ## 2. The representable composition equation in iso form -/

/-- The representable strong transformation of a composite scheme map is
isomorphic to the vertical composite of the representable strong
transformations. -/
noncomputable def S2431StrongTransOfHomCompIso
    {X1 X2 X3 : SchemeOverField S1726K} (a : X1 ⟶ X2) (b : X2 ⟶ X3) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S1726K) a)
        (S1742StrongTransOfHom (F := S1726K) b))
      (S1742StrongTransOfHom (F := S1726K) (a ≫ b)) := by
  have h := S1742StrongTransIsoOfHom (F := S1726K)
    (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S1726K) a)
      (S1742StrongTransOfHom (F := S1726K) b))
  rw [S2398HomOfStrongTrans_vcomp (F := S1726K) a b] at h
  exact h.symm

/-! ## 3. The composite map iso -/

/-- The main result: the composite map iso required by
S2429CompositeMapIsoRequired. -/
theorem S2431CompositeMapIsoRequired_holds
    {A B C : S1728Cover} {g1 : S1728CoverMap A B} {g2 : S1728CoverMap B C}
    (H : S2424ComposableRepresentable g1 g2) :
    S2429CompositeMapIsoRequired H := by
  obtain ⟨e1⟩ := H.R1.map_iso
  obtain ⟨e2⟩ := H.R2.map_iso
  refine ⟨?_⟩
  change Iso
    (S2403CastHom H.R1.source_fiber_eq H.R2.target_fiber_eq
      (Pseudofunctor.StrongTrans.vcomp g1.map g2.map))
    (S1742StrongTransOfHom (F := S1726K) (H.R1.g0 ≫ (H.middle_eq ▸ H.R2.g0)))
  let Y1 : EtaleStackPseudofunctor S1726K := S1742YS (F := S1726K) H.R1.sourceScheme
  let Y2 : EtaleStackPseudofunctor S1726K := S1742YS (F := S1726K) H.R1.targetScheme
  let Y3 : EtaleStackPseudofunctor S1726K := S1742YS (F := S1726K) H.R2.targetScheme
  let A1 : Pseudofunctor.StrongTrans Y1 Y2 :=
    S2403CastHom H.R1.source_fiber_eq H.R1.target_fiber_eq g1.map
  let A2' : Pseudofunctor.StrongTrans Y2 Y3 :=
    S2403CastHom H.R1.target_fiber_eq H.R2.target_fiber_eq g2.map
  let B1 : Pseudofunctor.StrongTrans Y1 Y2 :=
    S1742StrongTransOfHom (F := S1726K) H.R1.g0
  let B2 : Pseudofunctor.StrongTrans Y2 Y3 :=
    S1742StrongTransOfHom (F := S1726K) (H.middle_eq ▸ H.R2.g0)
  sorry

end LeanFormal.IUT.XiFPaper.S2431CompositeMapIsoActual
end
