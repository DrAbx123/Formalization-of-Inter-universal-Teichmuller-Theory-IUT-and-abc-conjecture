import tmp.sheaf.xif.paper.S2574ReverseCoverMapActual
import tmp.sheaf.xif.paper.S1728CoverCategoryActual
import tmp.sheaf.xif.paper.S2630CastHelpersActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.XiFPaper.S2521RepresentableStackActual
open LeanFormal.IUT.XiFPaper.S2554CanonicalEssSurjActual
open LeanFormal.IUT.XiFPaper.S2562CorrectedEssSurjLiftUniqueActual
open LeanFormal.IUT.XiFPaper.S2567CanonicalDataTransportActual
open LeanFormal.IUT.XiFPaper.S2568CanonicalCoverCommutesActual
open LeanFormal.IUT.XiFPaper.S2569CoverMapActual
open LeanFormal.IUT.XiFPaper.S2572SpecializedCoverMapActual
open LeanFormal.IUT.XiFPaper.S2573OpaqueDefsActual
open LeanFormal.IUT.XiFPaper.S2574ReverseCoverMapActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S2630CastHelpersActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2575CoverIsoActual

noncomputable def S2575B (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    Iut.SchemeOverField S2480QiActual.F :=
  S2517CScheme (S2573C0' S map finiteEtale D)

theorem S2517TStack_scheme_fiber (B : Iut.SchemeOverField S2480QiActual.F) :
    (S2517TStack B).fiber = S1742YS B := rfl

noncomputable def S2575_id_iso (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    Iso (S1742StrongTransOfHom (𝟙 (S2575B S map finiteEtale D)))
      (Pseudofunctor.StrongTrans.id (S1742YS (S2575B S map finiteEtale D))) := by
  have harg : S1742HomOfStrongTrans
      (Pseudofunctor.StrongTrans.id (S1742YS (S2575B S map finiteEtale D)))
      = 𝟙 (S2575B S map finiteEtale D) :=
    homOfStrongTrans_id _
  have hid : S1742StrongTransOfHom
      (S1742HomOfStrongTrans
        (Pseudofunctor.StrongTrans.id (S1742YS (S2575B S map finiteEtale D))))
      = S1742StrongTransOfHom (𝟙 (S2575B S map finiteEtale D)) :=
    congrArg S1742StrongTransOfHom harg
  rw [← hid]
  exact S1742StrongTransIsoOfHom
    (Pseudofunctor.StrongTrans.id (S1742YS (S2575B S map finiteEtale D)))



theorem S2575_castStrongTrans_hom
    (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    let h := S2517TStack_scheme_fiber (S2575B S map finiteEtale D)
    let L := Pseudofunctor.StrongTrans.vcomp
      (S2573CoverMap S map finiteEtale D).map
      (S2574CoverMapBack S map finiteEtale D).map
    S1742HomOfStrongTrans (castStrongTrans h L)
      = S1742HomOfStrongTrans L := by
  dsimp only
  cases S2517TStack_scheme_fiber (S2575B S map finiteEtale D)
  rfl

#check S2575_castStrongTrans_hom
#print axioms S2575_castStrongTrans_hom


theorem S2575_fwd_iso
    (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    let h := S2517TStack_scheme_fiber (S2575B S map finiteEtale D)
    let L := Pseudofunctor.StrongTrans.vcomp
      (S2573CoverMap S map finiteEtale D).map
      (S2574CoverMapBack S map finiteEtale D).map
    Nonempty (Iso (castStrongTrans h L)
      (Pseudofunctor.StrongTrans.id (S1742YS (S2575B S map finiteEtale D)))) := by
  dsimp only
  let h := S2517TStack_scheme_fiber (S2575B S map finiteEtale D)
  let L := Pseudofunctor.StrongTrans.vcomp
    (S2573CoverMap S map finiteEtale D).map
    (S2574CoverMapBack S map finiteEtale D).map
  have hf : (S2573CoverMap S map finiteEtale D).map
      = S1742StrongTransOfHom (S2573g S map finiteEtale D) :=
    (S2573CoverMap_map S map finiteEtale D).trans (S2573_rfl S map finiteEtale D)
  have hb : (S2574CoverMapBack S map finiteEtale D).map
      = S1742StrongTransOfHom (S2574g_inv S map finiteEtale D) := rfl
  have hLhom : S1742HomOfStrongTrans L
      = 𝟙 (S2575B S map finiteEtale D) := by
    dsimp [L]
    rw [hf, hb, S1742HomOfStrongTrans_vcomp]
    rw [S1742HomOfStrongTrans_strongTransOfHom]
    rw [S1742HomOfStrongTrans_strongTransOfHom]
    exact S2574g_comp_inv S map finiteEtale D
  have hHom : S1742HomOfStrongTrans (castStrongTrans h L)
      = 𝟙 (S2575B S map finiteEtale D) := by
    rw [S2575_castStrongTrans_hom S map finiteEtale D]
    exact hLhom
  have e1 := (S1742StrongTransIsoOfHom (castStrongTrans h L)).symm
  rw [hHom] at e1
  exact ⟨e1.trans (S2575_id_iso S map finiteEtale D)⟩

#check S2575_fwd_iso
#print axioms S2575_fwd_iso


noncomputable def S2575_id_iso_gen (B : Iut.SchemeOverField S2480QiActual.F) :
    Iso (S1742StrongTransOfHom (𝟙 B))
      (Pseudofunctor.StrongTrans.id (S1742YS B)) := by
  have harg : S1742HomOfStrongTrans
      (Pseudofunctor.StrongTrans.id (S1742YS B)) = 𝟙 B :=
    homOfStrongTrans_id _
  have hid : S1742StrongTransOfHom
      (S1742HomOfStrongTrans (Pseudofunctor.StrongTrans.id (S1742YS B)))
      = S1742StrongTransOfHom (𝟙 B) :=
    congrArg S1742StrongTransOfHom harg
  rw [← hid]
  exact S1742StrongTransIsoOfHom (Pseudofunctor.StrongTrans.id (S1742YS B))

theorem S2575_castStrongTrans_hom_S
    (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    let h := S2517TStack_scheme_fiber S
    let L := Pseudofunctor.StrongTrans.vcomp
      (S2574CoverMapBack S map finiteEtale D).map
      (S2573CoverMap S map finiteEtale D).map
    S1742HomOfStrongTrans (castStrongTrans h L)
      = S1742HomOfStrongTrans L := by
  dsimp only
  cases S2517TStack_scheme_fiber S
  rfl

theorem S2575_back_iso
    (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    let h := S2517TStack_scheme_fiber S
    let L := Pseudofunctor.StrongTrans.vcomp
      (S2574CoverMapBack S map finiteEtale D).map
      (S2573CoverMap S map finiteEtale D).map
    Nonempty (Iso (castStrongTrans h L)
      (Pseudofunctor.StrongTrans.id (S1742YS S))) := by
  dsimp only
  let h := S2517TStack_scheme_fiber S
  let L := Pseudofunctor.StrongTrans.vcomp
    (S2574CoverMapBack S map finiteEtale D).map
    (S2573CoverMap S map finiteEtale D).map
  have hf : (S2573CoverMap S map finiteEtale D).map
      = S1742StrongTransOfHom (S2573g S map finiteEtale D) :=
    (S2573CoverMap_map S map finiteEtale D).trans (S2573_rfl S map finiteEtale D)
  have hb : (S2574CoverMapBack S map finiteEtale D).map
      = S1742StrongTransOfHom (S2574g_inv S map finiteEtale D) := rfl
  have hLhom : S1742HomOfStrongTrans L = 𝟙 S := by
    dsimp [L]
    rw [hb, hf, S1742HomOfStrongTrans_vcomp]
    rw [S1742HomOfStrongTrans_strongTransOfHom]
    rw [S1742HomOfStrongTrans_strongTransOfHom]
    exact S2574g_inv_comp S map finiteEtale D
  have hHom : S1742HomOfStrongTrans (castStrongTrans h L) = 𝟙 S := by
    rw [S2575_castStrongTrans_hom_S S map finiteEtale D]
    exact hLhom
  have e1 := (S1742StrongTransIsoOfHom (castStrongTrans h L)).symm
  rw [hHom] at e1
  exact ⟨e1.trans (S2575_id_iso_gen S)⟩

#check S2575_back_iso
#print axioms S2575_back_iso

#check S2575B
#check S2517TStack_scheme_fiber
#check S2575_id_iso
#print axioms S2575_id_iso
end LeanFormal.IUT.XiFPaper.S2575CoverIsoActual
end
