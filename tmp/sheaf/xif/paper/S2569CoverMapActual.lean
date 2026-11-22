import tmp.sheaf.xif.paper.S2568CanonicalCoverCommutesActual

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
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2569CoverMapActual

noncomputable def S2569CoverMap
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
    (S2517InvObj C0').source.Hom X.source :=
  let C0 := S2554CanonicalCover X S hS D
  let S' := S2517CScheme C0
  let hsch : S' = S := S2562CanonicalCover_scheme (X := X) (S := S) hS D
  let hS' : X.source = S2517TStack S' := hS.trans (congrArg S2517TStack hsch.symm)
  let D' : S2554CanonicalData X S' hS' := S2567CanonicalData_transport X S S' hS hS' hsch D
  let C0' := S2554CanonicalCover X S' hS' D'
  let hsch' : S2517CScheme C0' = S' := S2562CanonicalCover_scheme (X := X) (S := S') hS' D'
  let g : S2517CScheme C0' ⟶ S := eqToHom hsch' ≫ eqToHom hsch
  @Eq.ndrec (Iut.EtaleStackOverField F) (S2517TStack S)
    (fun Z => (S2517InvObj C0').source.Hom Z)
    (S1742StrongTransOfHom g) X.source hS.symm

#check S2569CoverMap
end LeanFormal.IUT.XiFPaper.S2569CoverMapActual
end
