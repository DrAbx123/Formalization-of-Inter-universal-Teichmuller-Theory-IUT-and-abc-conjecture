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
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2584UncastProbeAdapted

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

end LeanFormal.IUT.XiFPaper.S2584UncastProbeAdapted
end
