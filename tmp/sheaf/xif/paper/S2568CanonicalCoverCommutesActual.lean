import tmp.sheaf.xif.paper.S2567CanonicalDataTransportActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2521RepresentableStackActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2554CanonicalEssSurjActual
open LeanFormal.IUT.XiFPaper.S2562CorrectedEssSurjLiftUniqueActual
open LeanFormal.IUT.XiFPaper.S2566CanonicalMapTransportActual
open LeanFormal.IUT.XiFPaper.S2567CanonicalDataTransportActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2568CanonicalCoverCommutesActual

theorem S2568eqToHom_comp_canonical
    (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve)
    (S : Iut.SchemeOverField F)
    (hS : X.source = S2517TStack S)
    (D : S2554CanonicalData X S hS) :
    (eqToIso (congrArg CategoryTheory.Over.left
      (S2562CanonicalCover_scheme (X := X) (S := S) hS D))).hom
      ≫ CategoryTheory.Over.Hom.left (S2554CanonicalMap X S hS)
      = (S2554CanonicalCover X S hS D).obj.hom := by
  dsimp [S2554CanonicalCover]
  rfl

theorem S2568eqToHom_comp_canonical_transport
    (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve)
    (S S' : Iut.SchemeOverField F)
    (hS : X.source = S2517TStack S)
    (hS' : X.source = S2517TStack S')
    (h : S' = S) :
    (eqToIso (congrArg CategoryTheory.Over.left h)).hom
      ≫ CategoryTheory.Over.Hom.left (S2554CanonicalMap X S hS)
      = CategoryTheory.Over.Hom.left (S2554CanonicalMap X S' hS') := by
  have hcanon := S2566CanonicalMap_eq X S S' hS hS' h
  have hf' : S2554CanonicalMap X S' hS' = h ▸ S2554CanonicalMap X S hS := by
    have := congrArg (fun x => h ▸ x) hcanon
    have hh := S2567transport_transport h (S2554CanonicalMap X S' hS')
    simpa [hh] using this
  rw [S2567eqToHom_comp_left (h := h)]
  exact (congrArg CategoryTheory.Over.Hom.left hf').symm



theorem S2568coverMap_commutes
    (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve)
    (S : Iut.SchemeOverField F)
    (hS : X.source = S2517TStack S)
    (D : S2554CanonicalData X S hS) :
    let C0 := S2554CanonicalCover X S hS D
    let S' := S2517CScheme C0
    let hsch : S' = S := S2562CanonicalCover_scheme (X := X) (S := S) hS D
    let hS' : X.source = S2517TStack S' := hS.trans (congrArg S2517TStack hsch.symm)
    let D' : S2554CanonicalData X S' hS' := S2567CanonicalData_transport X S S' hS hS' hsch D
    let C0' := S2554CanonicalCover X S' hS' D'
    let hsch' : S2517CScheme C0' = S' := S2562CanonicalCover_scheme (X := X) (S := S') hS' D'
    (eqToIso (congrArg CategoryTheory.Over.left hsch')).hom
      ≫ (eqToIso (congrArg CategoryTheory.Over.left hsch)).hom
      ≫ CategoryTheory.Over.Hom.left (S2554CanonicalMap X S hS)
      = C0'.obj.hom := by
  set C0 := S2554CanonicalCover X S hS D
  set S' := S2517CScheme C0
  set hsch : S' = S := S2562CanonicalCover_scheme (X := X) (S := S) hS D
  set hS' : X.source = S2517TStack S' := hS.trans (congrArg S2517TStack hsch.symm)
  set D' : S2554CanonicalData X S' hS' := S2567CanonicalData_transport X S S' hS hS' hsch D
  set C0' := S2554CanonicalCover X S' hS' D'
  set hsch' : S2517CScheme C0' = S' := S2562CanonicalCover_scheme (X := X) (S := S') hS' D'
  change (eqToIso (congrArg CategoryTheory.Over.left hsch')).hom
      ≫ (eqToIso (congrArg CategoryTheory.Over.left hsch)).hom
      ≫ CategoryTheory.Over.Hom.left (S2554CanonicalMap X S hS)
      = C0'.obj.hom
  have h1 := S2568eqToHom_comp_canonical X S' hS' D'
  have h2 := S2568eqToHom_comp_canonical_transport X S S' hS hS' hsch
  rw [h2, h1]

#check S2568eqToHom_comp_canonical
#check S2568eqToHom_comp_canonical_transport
#check S2568eqToHom_comp_canonical
#print axioms S2568eqToHom_comp_canonical
#check S2568coverMap_commutes
#print axioms S2568eqToHom_comp_canonical_transport
#print axioms S2568coverMap_commutes
end LeanFormal.IUT.XiFPaper.S2568CanonicalCoverCommutesActual
end
