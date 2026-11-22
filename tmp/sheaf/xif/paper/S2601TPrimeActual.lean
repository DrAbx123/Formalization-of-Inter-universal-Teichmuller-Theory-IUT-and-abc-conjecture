import tmp.sheaf.xif.paper.S2600TIntegralClosureActual
import tmp.sheaf.xif.paper.S2536LocalizedPowersActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace LeanFormal.IUT.XiFPaper.S2601TPrimeActual

open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
open LeanFormal.IUT.XiFPaper.S2599TInstancesActual

/-- S is the localization at powers (Cden : C). -/
local instance isLocS : IsLocalization (Submonoid.powers (Cden : C)) S := by
  have h := LeanFormal.IUT.XiFPaper.S2600TIntegralClosureActual.N_eq_powers
  rw [← h]
  exact inferInstance

/-- T' = O_L[1/Cden] as a localization of O_L at the image powers. -/
abbrev T' : Type := Localization (Algebra.algebraMapSubmonoid OL (Submonoid.powers (Cden : C)))

example : Algebra S T' := inferInstance

example : IsScalarTower C S T' := inferInstance

end LeanFormal.IUT.XiFPaper.S2601TPrimeActual
end