import tmp.sheaf.xif.paper.S2572SpecializedCoverMapActual

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
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2573OpaqueDefsActual

noncomputable def S2573C0 (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    FiniteEtaleCover S2482AffineScheme :=
  S2554CanonicalCover (X0 S map finiteEtale) S rfl D

noncomputable def S2573S' (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    Iut.SchemeOverField S2480QiActual.F :=
  S2517CScheme (S2573C0 S map finiteEtale D)

noncomputable def S2573hsch (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    S2573S' S map finiteEtale D = S :=
  S2562CanonicalCover_scheme (X := X0 S map finiteEtale) (S := S) rfl D

noncomputable def S2573hS' (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    (X0 S map finiteEtale).source = S2517TStack (S2573S' S map finiteEtale D) :=
  rfl.trans (congrArg S2517TStack (S2573hsch S map finiteEtale D).symm)

noncomputable def S2573D' (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    S2554CanonicalData (X0 S map finiteEtale) (S2573S' S map finiteEtale D)
      (S2573hS' S map finiteEtale D) :=
  S2567CanonicalData_transport (X0 S map finiteEtale) S (S2573S' S map finiteEtale D)
    rfl (S2573hS' S map finiteEtale D) (S2573hsch S map finiteEtale D) D

noncomputable def S2573C0' (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    FiniteEtaleCover S2482AffineScheme :=
  S2554CanonicalCover (X0 S map finiteEtale) (S2573S' S map finiteEtale D)
    (S2573hS' S map finiteEtale D) (S2573D' S map finiteEtale D)

noncomputable def S2573g (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    S2517CScheme (S2573C0' S map finiteEtale D) ⟶ S :=
  eqToHom (S2562CanonicalCover_scheme (X := X0 S map finiteEtale)
      (S := S2573S' S map finiteEtale D) (S2573hS' S map finiteEtale D)
      (S2573D' S map finiteEtale D)) ≫
    eqToHom (S2573hsch S map finiteEtale D)

theorem S2573_rfl (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    S2569CoverMap (X0 S map finiteEtale) S rfl D
      = S1742StrongTransOfHom (S2573g S map finiteEtale D) := by
  rfl


theorem S2573_hHom_spec (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    S1742HomOfStrongTrans
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (S2573g S map finiteEtale D))
        (X0 S map finiteEtale).map)
      = S2573g S map finiteEtale D ≫ S2554CanonicalMap (X0 S map finiteEtale) S rfl := by
  simpa [S2573g] using S2572_hHom_spec (S := S) (map := map) (finiteEtale := finiteEtale) (D := D)

theorem S2573Over_eq (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    S2573g S map finiteEtale D ≫ S2554CanonicalMap (X0 S map finiteEtale) S rfl
      = S2517OverMap (S2573C0' S map finiteEtale D) := by
  simpa [S2573g, S2573C0', S2573S', S2573hS', S2573D', S2573C0] using S2572Over_eq (S := S) (map := map) (finiteEtale := finiteEtale) (D := D)

noncomputable def S2573CoverMap (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    Iut.OrbicurveFiniteEtaleCoverMap
      (S2517InvObj (S2573C0' S map finiteEtale D))
      (X0 S map finiteEtale) := by
  let eta := Pseudofunctor.StrongTrans.vcomp
    (S1742StrongTransOfHom (S2573g S map finiteEtale D))
    (X0 S map finiteEtale).map
  have heta : Pseudofunctor.StrongTrans.vcomp
      (S2569CoverMap (X0 S map finiteEtale) S rfl D)
      (X0 S map finiteEtale).map = eta :=
    congrArg (fun L => Pseudofunctor.StrongTrans.vcomp L (X0 S map finiteEtale).map)
      (S2573_rfl S map finiteEtale D)
  have hHom : S1742HomOfStrongTrans eta
      = S2517OverMap (S2573C0' S map finiteEtale D) :=
    (S2573_hHom_spec S map finiteEtale D).trans (S2573Over_eq S map finiteEtale D)
  have hIso := (S1742StrongTransIsoOfHom eta).symm
  rw [hHom] at hIso
  refine { map := S2569CoverMap (X0 S map finiteEtale) S rfl D, commutes := ?_ }
  change Iso
    (Pseudofunctor.StrongTrans.vcomp
      (S2569CoverMap (X0 S map finiteEtale) S rfl D)
      (X0 S map finiteEtale).map)
    (S2517InvObj (S2573C0' S map finiteEtale D)).map
  exact (eqToIso heta).trans hIso


theorem S2573CoverMap_map (S : Iut.SchemeOverField S2480QiActual.F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    (S2573CoverMap S map finiteEtale D).map
      = S2569CoverMap (X0 S map finiteEtale) S rfl D := rfl

#check S2573C0
#check S2573C0'
#check S2573g
#check S2573_rfl
#print axioms S2573_rfl
#check S2573CoverMap
#check S2573CoverMap_map
#print axioms S2573CoverMap
end LeanFormal.IUT.XiFPaper.S2573OpaqueDefsActual
end
