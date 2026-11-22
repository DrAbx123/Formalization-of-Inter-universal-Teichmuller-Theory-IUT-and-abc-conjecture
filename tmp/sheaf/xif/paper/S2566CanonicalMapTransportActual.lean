import tmp.sheaf.xif.paper.S2565CanonicalCoverMapCastActual
import tmp.sheaf.xif.paper.S2554CanonicalEssSurjActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2521RepresentableStackActual
open LeanFormal.IUT.XiFPaper.S2554CanonicalEssSurjActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2566CanonicalMapTransportActual

theorem S2566CanonicalMap_eq
    (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve)
    (S S' : Iut.SchemeOverField F)
    (hS : X.source = S2517TStack S)
    (hS' : X.source = S2517TStack S')
    (h : S' = S) :
    h ▸ S2554CanonicalMap X S' hS' = S2554CanonicalMap X S hS := by
  cases h
  congr 1

#check S2566CanonicalMap_eq
#print axioms S2566CanonicalMap_eq
end LeanFormal.IUT.XiFPaper.S2566CanonicalMapTransportActual
end