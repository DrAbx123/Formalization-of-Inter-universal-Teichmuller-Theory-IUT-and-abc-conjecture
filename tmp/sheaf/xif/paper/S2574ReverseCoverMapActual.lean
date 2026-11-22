import tmp.sheaf.xif.paper.S2573OpaqueDefsActual
import tmp.sheaf.xif.paper.S1742HomVcompActual

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
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2574ReverseCoverMapActual

noncomputable def S2574hsch' (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    S2517CScheme (S2573C0' S map finiteEtale D) = S2573S' S map finiteEtale D :=
  S2562CanonicalCover_scheme (X := X0 S map finiteEtale)
    (S := S2573S' S map finiteEtale D) (S2573hS' S map finiteEtale D)
    (S2573D' S map finiteEtale D)

noncomputable def S2574g_inv (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    S ⟶ S2517CScheme (S2573C0' S map finiteEtale D) :=
  eqToHom (S2573hsch S map finiteEtale D).symm
    ≫ eqToHom (S2574hsch' S map finiteEtale D).symm

theorem S2574g_comp_inv (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    (S2573g S map finiteEtale D) ≫ (S2574g_inv S map finiteEtale D)
      = 𝟙 (S2517CScheme (S2573C0' S map finiteEtale D)) := by
  simp only [S2573g, S2574g_inv, eqToHom_trans, eqToHom_refl, Category.comp_id, Category.id_comp]

theorem S2574g_inv_comp (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    (S2574g_inv S map finiteEtale D) ≫ (S2573g S map finiteEtale D) = 𝟙 S := by
  simp only [S2573g, S2574g_inv, eqToHom_trans, eqToHom_refl, Category.comp_id, Category.id_comp]

noncomputable def S2574CoverMapBack (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    Iut.OrbicurveFiniteEtaleCoverMap
      (X0 S map finiteEtale)
      (S2517InvObj (S2573C0' S map finiteEtale D)) := by
  let eta := Pseudofunctor.StrongTrans.vcomp
    (S1742StrongTransOfHom (S2574g_inv S map finiteEtale D))
    (S2517InvObj (S2573C0' S map finiteEtale D)).map
  have hHom : S1742HomOfStrongTrans eta
      = S2554CanonicalMap (X0 S map finiteEtale) S rfl := by
    dsimp [eta, S2517InvObj, S2517StackHomOrb]
    rw [S1742HomOfStrongTrans_vcomp]
    rw [S1742HomOfStrongTrans_strongTransOfHom]
    rw [S1742HomOfStrongTrans_strongTransOfHom]
    rw [← S2573Over_eq S map finiteEtale D]
    rw [← Category.assoc, S2574g_inv_comp, Category.id_comp]
  have hIso := (S1742StrongTransIsoOfHom eta).symm
  rw [hHom] at hIso
  have hIso2 := hIso.trans (S1742StrongTransIsoOfHom (X0 S map finiteEtale).map)
  refine { map := S1742StrongTransOfHom (S2574g_inv S map finiteEtale D), commutes := ?_ }
  change Iso
    (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (S2574g_inv S map finiteEtale D))
      (S2517InvObj (S2573C0' S map finiteEtale D)).map)
    (X0 S map finiteEtale).map
  exact hIso2

#check S2574CoverMapBack
#print axioms S2574CoverMapBack
end LeanFormal.IUT.XiFPaper.S2574ReverseCoverMapActual
end
