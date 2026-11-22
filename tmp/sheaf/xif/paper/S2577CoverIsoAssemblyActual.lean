import tmp.sheaf.xif.paper.S2575CoverIsoActual
import tmp.sheaf.xif.paper.S2576CoverIsoFinalActual
import tmp.sheaf.xif.paper.S2562CorrectedEssSurjLiftUniqueActual

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
open LeanFormal.IUT.XiFPaper.S2575CoverIsoActual
open LeanFormal.IUT.XiFPaper.S2576CoverIsoFinalActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2577CoverIsoAssemblyActual

noncomputable def S2577CoverIso
    (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl)
    (hfw : S1728CoverMapRel
      (S1641CoverMapComp
        (S2573CoverMap S map finiteEtale D)
        (S2574CoverMapBack S map finiteEtale D))
      (S1641CoverMapId (S2517InvObj (S2573C0' S map finiteEtale D))))
    (hbk : S1728CoverMapRel
      (S1641CoverMapComp
        (S2574CoverMapBack S map finiteEtale D)
        (S2573CoverMap S map finiteEtale D))
      (S1641CoverMapId (X0 S map finiteEtale))) :
    S2517InvObj (S2573C0' S map finiteEtale D) ≅ X0 S map finiteEtale := by
  letI : Category (Iut.OrbicurveFiniteEtaleCover S2482Orbicurve) :=
    S1728CoverCategory11
  let A' := S2517InvObj (S2573C0' S map finiteEtale D)
  let X0' := X0 S map finiteEtale
  let fwd : Iut.OrbicurveFiniteEtaleCoverMap A' X0' := S2573CoverMap S map finiteEtale D
  let back : Iut.OrbicurveFiniteEtaleCoverMap X0' A' := S2574CoverMapBack S map finiteEtale D
  let hom1 : A' ⟶ X0' :=
    Quot.mk (fun f g : Iut.OrbicurveFiniteEtaleCoverMap A' X0' => S1728CoverMapRel f g) fwd
  let hom2 : X0' ⟶ A' :=
    Quot.mk (fun f g : Iut.OrbicurveFiniteEtaleCoverMap X0' A' => S1728CoverMapRel f g) back
  have hcomp : hom1 ≫ hom2
      = Quot.mk (fun f g : Iut.OrbicurveFiniteEtaleCoverMap A' A' => S1728CoverMapRel f g) (S1641CoverMapId A') := by
    change S1728CoverMapClassComp hom1 hom2 = S1728CoverMapClassId A'
    rw [show S1728CoverMapClassComp hom1 hom2
        = Quot.mk _ (S1641CoverMapComp fwd back) by
      simp [hom1, hom2, S1728CoverMapClassComp, Quot.map₂_mk]]
    exact Quot.sound hfw
  have hcomp' : hom2 ≫ hom1
      = Quot.mk (fun f g : Iut.OrbicurveFiniteEtaleCoverMap X0' X0' => S1728CoverMapRel f g) (S1641CoverMapId X0') := by
    change S1728CoverMapClassComp hom2 hom1 = S1728CoverMapClassId X0'
    rw [show S1728CoverMapClassComp hom2 hom1
        = Quot.mk _ (S1641CoverMapComp back fwd) by
      simp [hom1, hom2, S1728CoverMapClassComp, Quot.map₂_mk]]
    exact Quot.sound hbk
  exact CategoryTheory.Iso.mk hom1 hom2 hcomp hcomp'


theorem S2577CanonicalCoverIsoFromData
    (hfw : ∀ (S : Iut.SchemeOverField S2480QiActual.F)
      (map : (S2517TStack S).Hom S2482Orbicurve.stack)
      (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
      (D : S2554CanonicalData (X0 S map finiteEtale) S rfl),
      S1728CoverMapRel
        (S1641CoverMapComp
          (S2573CoverMap S map finiteEtale D)
          (S2574CoverMapBack S map finiteEtale D))
        (S1641CoverMapId (S2517InvObj (S2573C0' S map finiteEtale D))))
    (hbk : ∀ (S : Iut.SchemeOverField S2480QiActual.F)
      (map : (S2517TStack S).Hom S2482Orbicurve.stack)
      (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
      (D : S2554CanonicalData (X0 S map finiteEtale) S rfl),
      S1728CoverMapRel
        (S1641CoverMapComp
          (S2574CoverMapBack S map finiteEtale D)
          (S2573CoverMap S map finiteEtale D))
        (S1641CoverMapId (X0 S map finiteEtale))) :
    S2562CanonicalCoverIsoFromData := by
  intro X S hS D
  revert X hS D
  intro X hS D
  cases X with
  | mk source map finiteEtale =>
    cases hS
    exact ⟨S2577CoverIso S map finiteEtale D
      (hfw S map finiteEtale D) (hbk S map finiteEtale D)⟩

#check S2577CanonicalCoverIsoFromData
#print axioms S2577CanonicalCoverIsoFromData

#check S2577CoverIso
end LeanFormal.IUT.XiFPaper.S2577CoverIsoAssemblyActual
end
