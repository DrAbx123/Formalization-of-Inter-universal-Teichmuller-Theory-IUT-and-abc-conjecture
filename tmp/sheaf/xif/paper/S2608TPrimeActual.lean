import tmp.sheaf.xif.paper.S2599TInstancesActual
import tmp.sheaf.xif.paper.S2600TIntegralClosureActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace LeanFormal.IUT.XiFPaper.S2608TPrimeActual

open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
open LeanFormal.IUT.XiFPaper.S2599TInstancesActual

abbrev T' : Type := Localization (Algebra.algebraMapSubmonoid OL (Submonoid.powers (c : ℤ)))

example : Algebra S T' := inferInstance

example : IsScalarTower C S T' := inferInstance

end LeanFormal.IUT.XiFPaper.S2608TPrimeActual
end