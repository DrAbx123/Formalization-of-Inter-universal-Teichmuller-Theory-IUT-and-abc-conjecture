import tmp.sheaf.xif.paper.S2575CoverIsoActual
import tmp.sheaf.xif.paper.S2576CoverIsoFinalActual
import tmp.sheaf.xif.paper.S2578CastBothActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2521RepresentableStackActual
open LeanFormal.IUT.XiFPaper.S2554CanonicalEssSurjActual
open LeanFormal.IUT.XiFPaper.S2572SpecializedCoverMapActual
open LeanFormal.IUT.XiFPaper.S2573OpaqueDefsActual
open LeanFormal.IUT.XiFPaper.S2574ReverseCoverMapActual
open LeanFormal.IUT.XiFPaper.S2575CoverIsoActual
open LeanFormal.IUT.XiFPaper.S2576CoverIsoFinalActual
open LeanFormal.IUT.XiFPaper.S2630CastHelpersActual
open LeanFormal.IUT.XiFPaper.S2578CastBothActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2582E2Probe

universe u
variable {F : Type u} [Field F]
variable {P Q R S : Iut.EtaleStackPseudofunctor F}

noncomputable def castStrongTrans2 (h : P = Q) (k : R = S)
    (L : Pseudofunctor.StrongTrans P R) : Pseudofunctor.StrongTrans Q S := by
  cases h
  cases k
  exact L

noncomputable def castIso2 (h : P = Q) (k : R = S)
    {L1 L2 : Pseudofunctor.StrongTrans P R} (e : Iso L1 L2) :
    Iso (castStrongTrans2 h k L1) (castStrongTrans2 h k L2) := by
  cases h
  cases k
  exact e

variable {S0 : Iut.SchemeOverField S2480QiActual.F}
variable {map : (S2517TStack S0).Hom S2482Orbicurve.stack}
variable {finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map}
variable {D : S2554CanonicalData (X0 S0 map finiteEtale) S0 rfl}

example : True := by
  obtain ⟨e⟩ := S2575_fwd_iso S0 map finiteEtale D
  let h := S2517TStack_scheme_fiber (S2575B S0 map finiteEtale D)
  let e2 := castIso2 h.symm h.symm e
  trace_state
  have hleft : castStrongTrans2 h.symm h.symm
      (castStrongTrans h
        (Pseudofunctor.StrongTrans.vcomp
          (S2573CoverMap S0 map finiteEtale D).map
          (S2574CoverMapBack S0 map finiteEtale D).map)) =
      Pseudofunctor.StrongTrans.vcomp
        (S2573CoverMap S0 map finiteEtale D).map
        (S2574CoverMapBack S0 map finiteEtale D).map := by
    cases h
    rfl
  have hright : castStrongTrans2 h.symm h.symm
      (Pseudofunctor.StrongTrans.id (S1742YS (S2575B S0 map finiteEtale D))) =
      Pseudofunctor.StrongTrans.id (S2517TStack (S2575B S0 map finiteEtale D)).fiber := by
    cases h
    rfl
  rw [hleft, hright] at e2
  trivial

end LeanFormal.IUT.XiFPaper.S2582E2Probe
end
