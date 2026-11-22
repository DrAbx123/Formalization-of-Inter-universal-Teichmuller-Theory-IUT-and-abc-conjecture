import tmp.sheaf.xif.paper.S2609SSPrimeActual
import tmp.sheaf.xif.paper.S2610TTPrimeActual
import tmp.sheaf.xif.paper.S2599TInstancesActual
import tmp.sheaf.xif.paper.S2605LiftSLActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace LeanFormal.IUT.XiFPaper.S2611TransportActual

abbrev Cb : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.C
abbrev Sb : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.S
abbrev T0 : Type := LeanFormal.IUT.XiFPaper.S2599TInstancesActual.T

open LeanFormal.IUT.XiFPaper.S2609SSPrimeActual
open LeanFormal.IUT.XiFPaper.S2599TInstancesActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2610TTPrimeActual
open LeanFormal.IUT.XiFPaper.S2609SSPrimeActual

noncomputable def phi : Sb →+* T0 :=
  eTT'.symm.toRingHom.comp ((algebraMap S' T').comp eSS'.toRingHom)

local instance : Algebra Sb T0 := phi.toAlgebra

end LeanFormal.IUT.XiFPaper.S2611TransportActual
end