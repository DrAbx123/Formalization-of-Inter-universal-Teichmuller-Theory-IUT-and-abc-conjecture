import tmp.sheaf.xif.paper.S2429CompositeAssemblyActual

/-!
# S2431: the composite map iso required by S2429CompositeMapIsoRequired

Given `H : S2424ComposableRepresentable g1 g2`, this file constructs

  `Nonempty (Iso
    (S2403CastHom H.R1.source_fiber_eq H.R2.target_fiber_eq (S1641CoverMapComp g1 g2).map)
    (S1742StrongTransOfHom (S2429CompositeMap H)))`.

The construction is:

* transport the second representability isomorphism `H.R2.map_iso` along the
  middle scheme equality `H.middle_eq` (section 1); the transport is a
  generalized lemma whose proof is a type-level `cases` on the scheme
  equality, so no dependent elimination on the structure projection
  `H.middle_eq` is attempted;
* the cast-composition lemma `S2429CastComp_holds` rewrites the cast of the
  vertical composite to the vertical composite of the two casts;
* the underlying scheme map of a vertical composite of representable strong
  transformations is the composite scheme map (section 2, from
  `S1742Key`), so `S1742HomOfStrongTrans` of the cast composite is
  `H.R1.g0 ≫ (H.middle_eq ▸ H.R2.g0)`;
* the 2-Yoneda round trip `S1742StrongTransIsoOfHom` then identifies the
  cast composite with `S1742StrongTransOfHom` of that scheme map.

No `sorry`, no new axiom, no change of target.  The only axioms used are
`propext`, `Classical.choice`, `Quot.sound`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
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
proof irrelevance.  The proof is a type-level `cases` on the scheme equality
only: all data (`h2`, `h2'`, `h3`, `g0`, `e`) are independent variables,
so there is no dependent elimination of a projection of `H`. -/
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

/-! ## 2. The underlying scheme map of a vertical composite -/

/-- The underlying scheme morphism of a vertical composite of representable
strong transformations is the composite scheme morphism.  This is the
`S1742Key` computation rule applied twice (at the source scheme of the
second factor via strong naturality). -/
theorem S2431HomOfStrongTrans_vcomp
    {S T U : SchemeOverField S1726K}
    (η : Pseudofunctor.StrongTrans (S1742YS (F := S1726K) S) (S1742YS (F := S1726K) T))
    (θ : Pseudofunctor.StrongTrans (S1742YS (F := S1726K) T) (S1742YS (F := S1726K) U)) :
    S1742HomOfStrongTrans (Pseudofunctor.StrongTrans.vcomp η θ) =
      S1742HomOfStrongTrans η ≫ S1742HomOfStrongTrans θ := by
  unfold S1742HomOfStrongTrans
  change (((η.app (LocallyDiscrete.mk (Opposite.op S))) ≫
      (θ.app (LocallyDiscrete.mk (Opposite.op S)))).toFunctor.obj (Discrete.mk (𝟙 S))).as
    = (((η.app (LocallyDiscrete.mk (Opposite.op S))).toFunctor.obj (Discrete.mk (𝟙 S))).as)
      ≫ (((θ.app (LocallyDiscrete.mk (Opposite.op T))).toFunctor.obj (Discrete.mk (𝟙 T))).as)
  rw [S1742Comp_toFunctor_obj]
  have hζη : (η.app (LocallyDiscrete.mk (Opposite.op S))).toFunctor.obj (Discrete.mk (𝟙 S))
      = Discrete.mk (S1742HomOfStrongTrans η) := Discrete.mk_as _
  have hζθ : (θ.app (LocallyDiscrete.mk (Opposite.op T))).toFunctor.obj (Discrete.mk (𝟙 T))
      = Discrete.mk (S1742HomOfStrongTrans θ) := Discrete.mk_as _
  rw [hζη, S1742Key θ (LocallyDiscrete.mk (Opposite.op S)) (S1742HomOfStrongTrans η)]
  rw [hζθ]

/-! ## 3. The composite map iso -/

/-- The main result: the composite map iso required by
`S2429CompositeMapIsoRequired H`. -/
theorem S2431CompositeMapIsoRequired_holds
    {A B C : S1728Cover} {g1 : S1728CoverMap A B} {g2 : S1728CoverMap B C}
    (H : S2424ComposableRepresentable g1 g2) :
    S2429CompositeMapIsoRequired H := by
  obtain ⟨e1⟩ := H.R1.map_iso
  obtain ⟨e2⟩ := H.R2.map_iso
  let L1 : Pseudofunctor.StrongTrans
      (S1742YS (F := S1726K) H.R1.sourceScheme)
      (S1742YS (F := S1726K) H.R1.targetScheme) :=
    S2403CastHom H.R1.source_fiber_eq H.R1.target_fiber_eq g1.map
  let L2 : Pseudofunctor.StrongTrans
      (S1742YS (F := S1726K) H.R1.targetScheme)
      (S1742YS (F := S1726K) H.R2.targetScheme) :=
    S2403CastHom H.R1.target_fiber_eq H.R2.target_fiber_eq g2.map
  let L : Pseudofunctor.StrongTrans
      (S1742YS (F := S1726K) H.R1.sourceScheme)
      (S1742YS (F := S1726K) H.R2.targetScheme) :=
    S2403CastHom H.R1.source_fiber_eq H.R2.target_fiber_eq (S1641CoverMapComp g1 g2).map
  have hcast : L = Pseudofunctor.StrongTrans.vcomp L1 L2 := by
    change S2403CastHom H.R1.source_fiber_eq H.R2.target_fiber_eq
      (Pseudofunctor.StrongTrans.vcomp g1.map g2.map) = _
    exact S2429CastComp_holds (A := A.source) (B := B.source) (C := C.source)
      (S1 := H.R1.sourceScheme) (S2 := H.R1.targetScheme) (S3 := H.R2.targetScheme)
      H.R1.source_fiber_eq H.R1.target_fiber_eq H.R2.target_fiber_eq g1.map g2.map
  have h1 : S1742HomOfStrongTrans (F := S1726K) L1 = H.R1.g0 :=
    (S1742HomOfStrongTrans_congr (F := S1726K) e1).trans
      (S1742HomOfStrongTrans_strongTransOfHom (F := S1726K) H.R1.g0)
  have h2 : S1742HomOfStrongTrans (F := S1726K) L2 = H.middle_eq ▸ H.R2.g0 :=
    (S1742HomOfStrongTrans_congr (F := S1726K)
      (S2431CastHomMidIso (B := B.source) (C := C.source)
        (X2 := H.R1.targetScheme) (X2' := H.R2.sourceScheme) (X3 := H.R2.targetScheme)
        H.R1.target_fiber_eq H.R2.source_fiber_eq H.middle_eq H.R2.target_fiber_eq
        g2.map H.R2.g0 e2)).trans
      (S1742HomOfStrongTrans_strongTransOfHom (F := S1726K) (H.middle_eq ▸ H.R2.g0))
  have hL : S1742HomOfStrongTrans (F := S1726K) L
      = H.R1.g0 ≫ (H.middle_eq ▸ H.R2.g0) := by
    calc S1742HomOfStrongTrans (F := S1726K) L
        = S1742HomOfStrongTrans (F := S1726K) (Pseudofunctor.StrongTrans.vcomp L1 L2) :=
          congrArg (S1742HomOfStrongTrans (F := S1726K)) hcast
      _ = S1742HomOfStrongTrans (F := S1726K) L1 ≫ S1742HomOfStrongTrans (F := S1726K) L2 :=
          S2431HomOfStrongTrans_vcomp L1 L2
      _ = H.R1.g0 ≫ (H.middle_eq ▸ H.R2.g0) := by rw [h1, h2]
  refine ⟨?_⟩
  change Iso L (S1742StrongTransOfHom (F := S1726K) (H.R1.g0 ≫ (H.middle_eq ▸ H.R2.g0)))
  exact (S1742StrongTransIsoOfHom (F := S1726K) L).symm.trans
    (eqToIso (congrArg (S1742StrongTransOfHom (F := S1726K)) hL))


/-- Integration: S2424 composite representability is now actual for every
composable pair of representable cover maps. -/
theorem S2431S2424CompositionRequired
    {A B C : S1728Cover} {g1 : S1728CoverMap A B} {g2 : S1728CoverMap B C}
    (H : S2424ComposableRepresentable g1 g2) :
    S2424CompositionRequired H :=
  S2424CompositionRequired_of_mapIso H
    (S2431CompositeMapIsoRequired_holds H)


end LeanFormal.IUT.XiFPaper.S2431CompositeMapIsoActual
end