import tmp.sheaf.xif.paper.S2605LiftSLActual
import tmp.sheaf.xif.paper.S2600TIntegralClosureActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace LeanFormal.IUT.XiFPaper.S2609SSPrimeActual

open LeanFormal.IUT.XiFPaper.S2605LiftSLActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual

abbrev M : Submonoid Cb := Submonoid.powers ((algebraMap ℤ Cb c) : Cb)
abbrev N : Submonoid Cb := Algebra.algebraMapSubmonoid Cb (Submonoid.powers (c : ℤ))
abbrev S' : Type := Localization M

lemma hMN : N = M := LeanFormal.IUT.XiFPaper.S2600TIntegralClosureActual.N_eq_powers

local instance hlocS : IsLocalization M Sb := by
  rw [← hMN]
  exact Localization.isLocalization

noncomputable def eSS' : Sb ≃+* S' :=
  (IsLocalization.algEquiv M Sb S').toRingEquiv

end LeanFormal.IUT.XiFPaper.S2609SSPrimeActual
end