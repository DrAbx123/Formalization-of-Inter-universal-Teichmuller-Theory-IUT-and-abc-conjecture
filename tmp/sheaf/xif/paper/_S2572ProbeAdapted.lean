import tmp.sheaf.xif.paper.S2569CoverMapActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2521RepresentableStackActual
open LeanFormal.IUT.XiFPaper.S2554CanonicalEssSurjActual
noncomputable section
namespace Probe
example (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve)
    (S : Iut.SchemeOverField F) (hS : X.source = S2517TStack S)
    (D : S2554CanonicalData X S hS) : True := by
  revert X hS D
  intro X hS D
  cases X
  cases hS
  trivial
end Probe
