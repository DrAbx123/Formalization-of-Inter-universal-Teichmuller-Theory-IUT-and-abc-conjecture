import tmp.sheaf.xif.paper.S2571VcompCastTargetActual
import tmp.sheaf.xif.paper.S2569CoverMapActual
import tmp.sheaf.xif.paper.S2568CanonicalCoverCommutesActual
import tmp.sheaf.xif.paper.S2630CastHelpersActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual
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
open LeanFormal.IUT.XiFPaper.S2630CastHelpersActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2572SpecializedCoverMapActual

abbrev X0 (S : Iut.SchemeOverField F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map) :
    Iut.OrbicurveFiniteEtaleCover S2482Orbicurve :=
  { source := S2517TStack S, map := map, finiteEtale := finiteEtale }

theorem S2572_hcanon (S : Iut.SchemeOverField F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    S1742HomOfStrongTrans (X0 S map finiteEtale).map
      = S2554CanonicalMap (X0 S map finiteEtale) S rfl := by
  rfl

noncomputable def S2572_coverMap
    (S : Iut.SchemeOverField F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    let C0 := S2554CanonicalCover (X0 S map finiteEtale) S rfl D
    let S' := S2517CScheme C0
    let hsch : S' = S := S2562CanonicalCover_scheme (X := X0 S map finiteEtale) (S := S) rfl D
    let hS' : (X0 S map finiteEtale).source = S2517TStack S' := rfl.trans (congrArg S2517TStack hsch.symm)
    let D' : S2554CanonicalData (X0 S map finiteEtale) S' hS' := S2567CanonicalData_transport (X0 S map finiteEtale) S S' rfl hS' hsch D
    let C0' := S2554CanonicalCover (X0 S map finiteEtale) S' hS' D'
    (S2517InvObj C0').source.Hom (X0 S map finiteEtale).source := by
  dsimp only
  exact S2569CoverMap (X0 S map finiteEtale) S rfl D



theorem S2572S2569CoverMap_rfl
    (S : Iut.SchemeOverField F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    let C0 := S2554CanonicalCover (X0 S map finiteEtale) S rfl D
    let S' := S2517CScheme C0
    let hsch : S' = S := S2562CanonicalCover_scheme (X := X0 S map finiteEtale) (S := S) rfl D
    let hS' : (X0 S map finiteEtale).source = S2517TStack S' := rfl.trans (congrArg S2517TStack hsch.symm)
    let D' : S2554CanonicalData (X0 S map finiteEtale) S' hS' := S2567CanonicalData_transport (X0 S map finiteEtale) S S' rfl hS' hsch D
    let C0' := S2554CanonicalCover (X0 S map finiteEtale) S' hS' D'
    let hsch' : S2517CScheme C0' = S' := S2562CanonicalCover_scheme (X := X0 S map finiteEtale) (S := S') hS' D'
    S2569CoverMap (X0 S map finiteEtale) S rfl D
      = S1742StrongTransOfHom (eqToHom hsch' ≫ eqToHom hsch) := by
  rfl




set_option maxHeartbeats 20000000 in
theorem S2572_hHom_spec
    (S : Iut.SchemeOverField F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    let C0 := S2554CanonicalCover (X0 S map finiteEtale) S rfl D
    let S' := S2517CScheme C0
    let hsch : S' = S := S2562CanonicalCover_scheme (X := X0 S map finiteEtale) (S := S) rfl D
    let hS' : (X0 S map finiteEtale).source = S2517TStack S' := rfl.trans (congrArg S2517TStack hsch.symm)
    let D' : S2554CanonicalData (X0 S map finiteEtale) S' hS' := S2567CanonicalData_transport (X0 S map finiteEtale) S S' rfl hS' hsch D
    let C0' := S2554CanonicalCover (X0 S map finiteEtale) S' hS' D'
    let hsch' : S2517CScheme C0' = S' := S2562CanonicalCover_scheme (X := X0 S map finiteEtale) (S := S') hS' D'
    let g : S2517CScheme C0' ⟶ S := eqToHom hsch' ≫ eqToHom hsch
    S1742HomOfStrongTrans
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom g) (X0 S map finiteEtale).map)
      = g ≫ S2554CanonicalMap (X0 S map finiteEtale) S rfl := by
  dsimp only
  rw [S1742HomOfStrongTrans_vcomp]
  rw [S1742HomOfStrongTrans_strongTransOfHom]
  rw [S2572_hcanon (S := S) (map := map) (finiteEtale := finiteEtale) (D := D)]


theorem S2572Over_eq
    (S : Iut.SchemeOverField F)
    (map : (S2517TStack S).Hom S2482Orbicurve.stack)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map)
    (D : S2554CanonicalData (X0 S map finiteEtale) S rfl) :
    let C0 := S2554CanonicalCover (X0 S map finiteEtale) S rfl D
    let S' := S2517CScheme C0
    let hsch : S' = S := S2562CanonicalCover_scheme (X := X0 S map finiteEtale) (S := S) rfl D
    let hS' : (X0 S map finiteEtale).source = S2517TStack S' := rfl.trans (congrArg S2517TStack hsch.symm)
    let D' : S2554CanonicalData (X0 S map finiteEtale) S' hS' := S2567CanonicalData_transport (X0 S map finiteEtale) S S' rfl hS' hsch D
    let C0' := S2554CanonicalCover (X0 S map finiteEtale) S' hS' D'
    let hsch' : S2517CScheme C0' = S' := S2562CanonicalCover_scheme (X := X0 S map finiteEtale) (S := S') hS' D'
    let g : S2517CScheme C0' ⟶ S := eqToHom hsch' ≫ eqToHom hsch
    g ≫ S2554CanonicalMap (X0 S map finiteEtale) S rfl = S2517OverMap C0' := by
  dsimp only
  apply CategoryTheory.Over.OverMorphism.ext
  have h := S2568coverMap_commutes (X := X0 S map finiteEtale) S rfl D
  simpa [S2517OverMap, CategoryTheory.Over.Hom.left] using h



#check S2572_hcanon
#check S2572_coverMap
#check S2572S2569CoverMap_rfl
#check S2572_hHom_spec
#check S2572Over_eq
#print axioms S2572Over_eq
#print axioms S2572_hHom_spec
end LeanFormal.IUT.XiFPaper.S2572SpecializedCoverMapActual
end
