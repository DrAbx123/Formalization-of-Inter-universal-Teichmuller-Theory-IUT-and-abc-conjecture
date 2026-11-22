import tmp.sheaf.xif.paper.S2566CanonicalMapTransportActual
import tmp.sheaf.xif.paper.S2555ExtractionTransportActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2521RepresentableStackActual
open LeanFormal.IUT.XiFPaper.S2554CanonicalEssSurjActual
open LeanFormal.IUT.XiFPaper.S2555ExtractionTransportActual
open LeanFormal.IUT.XiFPaper.S2566CanonicalMapTransportActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2567CanonicalDataTransportActual

theorem S2567transport_transport
    {S S' : Iut.SchemeOverField F} (h : S' = S) (f : S' ⟶ S2482AffineOver) :
    h ▸ (h ▸ f) = f := by
  cases h
  rfl

theorem S2567eqToHom_comp_left
    {S S' : Iut.SchemeOverField F} (h : S' = S)
    (f : S ⟶ S2482AffineOver) :
    (eqToIso (congrArg CategoryTheory.Over.left h)).hom ≫ (CategoryTheory.Over.Hom.left f)
      = CategoryTheory.Over.Hom.left (h ▸ f) := by
  cases h
  rfl

def S2567CanonicalData_transport
    (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve)
    (S S' : Iut.SchemeOverField F)
    (hS : X.source = S2517TStack S)
    (hS' : X.source = S2517TStack S')
    (h : S' = S)
    (D : S2554CanonicalData X S hS) :
    S2554CanonicalData X S' hS' := by
  have hcanon := S2566CanonicalMap_eq X S S' hS hS' h
  have hleft : CategoryTheory.Over.Hom.left (h ▸ S2554CanonicalMap X S' hS')
      = CategoryTheory.Over.Hom.left (S2554CanonicalMap X S hS) :=
    congrArg CategoryTheory.Over.Hom.left hcanon
  have hf' : S2554CanonicalMap X S' hS' = h ▸ S2554CanonicalMap X S hS := by
    have := congrArg (fun x => h ▸ x) hcanon
    have hh := S2567transport_transport h (S2554CanonicalMap X S' hS')
    simpa [hh] using this
  have hleft' : CategoryTheory.Over.Hom.left (S2554CanonicalMap X S' hS')
      = CategoryTheory.Over.Hom.left (h ▸ S2554CanonicalMap X S hS) :=
    congrArg CategoryTheory.Over.Hom.left hf'
  have hrel : (eqToIso (congrArg CategoryTheory.Over.left h)).hom
      ≫ CategoryTheory.Over.Hom.left (S2554CanonicalMap X S hS)
      = CategoryTheory.Over.Hom.left (S2554CanonicalMap X S' hS') := by
    rw [S2567eqToHom_comp_left (h := h)]
    exact hleft'.symm
  exact
    { etale := S2555Etale_of_arrowIso
        (e := eqToIso (congrArg CategoryTheory.Over.left h)) hrel D.etale
      finite := S2555IsFinite_of_arrowIso
        (e := eqToIso (congrArg CategoryTheory.Over.left h)) hrel D.finite }

#check S2567eqToHom_comp_left
#check S2567CanonicalData_transport
#print axioms S2567CanonicalData_transport
end LeanFormal.IUT.XiFPaper.S2567CanonicalDataTransportActual
end