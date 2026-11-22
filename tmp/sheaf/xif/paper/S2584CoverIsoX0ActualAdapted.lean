import tmp.sheaf.xif.paper.S2575CoverIsoActual
import tmp.sheaf.xif.paper.S2576CoverIsoFinalActual
import tmp.sheaf.xif.paper.S2583CastIso2Actual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.XiFPaper.S2521RepresentableStackActual
open LeanFormal.IUT.XiFPaper.S2554CanonicalEssSurjActual
open LeanFormal.IUT.XiFPaper.S2572SpecializedCoverMapActual
open LeanFormal.IUT.XiFPaper.S2573OpaqueDefsActual
open LeanFormal.IUT.XiFPaper.S2574ReverseCoverMapActual
open LeanFormal.IUT.XiFPaper.S2575CoverIsoActual
open LeanFormal.IUT.XiFPaper.S2576CoverIsoFinalActual
open LeanFormal.IUT.XiFPaper.S2630CastHelpersActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2584CoverIsoX0ActualAdapted

variable {S : Iut.SchemeOverField S2480QiActual.F}
variable {map : (S2517TStack S).Hom S2482Orbicurve.stack}
variable {finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map}
variable {D : S2554CanonicalData (X0 S map finiteEtale) S rfl}

example :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (S2573CoverMap S map finiteEtale D).map
        (S2574CoverMapBack S map finiteEtale D).map)
      (Pseudofunctor.StrongTrans.id
        (S2517InvObj (S2573C0' S map finiteEtale D)).source.fiber) := by
  let B := S2575B S map finiteEtale D
  let L : Pseudofunctor.StrongTrans (S2517TStack B).fiber (S2517TStack B).fiber :=
    Pseudofunctor.StrongTrans.vcomp
      (S2573CoverMap S map finiteEtale D).map
      (S2574CoverMapBack S map finiteEtale D).map
  let e := Classical.choice (S2575_fwd_iso S map finiteEtale D)
  let uncast :
      Iso (castStrongTrans (S2517TStack_scheme_fiber B) L)
        (Pseudofunctor.StrongTrans.id (S1742YS B)) ->
      Iso L (Pseudofunctor.StrongTrans.id (S2517TStack B).fiber) :=
    fun e => by
      cases S2517TStack_scheme_fiber B
      exact e
  exact uncast e
/-- The X0 cover Iso from the uncast fwd/back Isos. -/
noncomputable def S2584CoverIsoX0 :
    Iso (S2517InvObj (S2573C0' S map finiteEtale D)) (X0 S map finiteEtale) where
  hom := Quot.mk _ (S2573CoverMap S map finiteEtale D)
  inv := Quot.mk _ (S2574CoverMapBack S map finiteEtale D)
  hom_inv_id := by
    apply Quot.sound
    let C := S2517CScheme (S2573C0' S map finiteEtale D)
    let L : Pseudofunctor.StrongTrans (S2517TStack C).fiber (S2517TStack C).fiber :=
      Pseudofunctor.StrongTrans.vcomp
        (S2573CoverMap S map finiteEtale D).map
        (S2574CoverMapBack S map finiteEtale D).map
    let e := Classical.choice (S2575_fwd_iso S map finiteEtale D)
    let e' : Iso L (Pseudofunctor.StrongTrans.id (S2517TStack C).fiber) :=
      (by
        change Iso L (Pseudofunctor.StrongTrans.id
          (S2517TStack (S2575B S map finiteEtale D)).fiber)
        cases S2517TStack_scheme_fiber (S2575B S map finiteEtale D)
        exact e)
    exact ⟨by simpa [S1641CoverMapComp_map, S1641CoverMapId_map, S2517InvObj, S2575B] using e'⟩
  inv_hom_id := by
    apply Quot.sound
    let L : Pseudofunctor.StrongTrans (S2517TStack S).fiber (S2517TStack S).fiber :=
      Pseudofunctor.StrongTrans.vcomp
      (S2574CoverMapBack S map finiteEtale D).map
      (S2573CoverMap S map finiteEtale D).map
    let e := Classical.choice (S2575_back_iso S map finiteEtale D)
    let e' : Iso L (Pseudofunctor.StrongTrans.id (S2517TStack S).fiber) :=
      (by
        cases S2517TStack_scheme_fiber S
        exact e)
    exact ⟨by simpa [S1641CoverMapComp_map, S1641CoverMapId_map, S2517InvObj] using e'⟩

#print axioms S2584CoverIsoX0

end LeanFormal.IUT.XiFPaper.S2584CoverIsoX0ActualAdapted
end
