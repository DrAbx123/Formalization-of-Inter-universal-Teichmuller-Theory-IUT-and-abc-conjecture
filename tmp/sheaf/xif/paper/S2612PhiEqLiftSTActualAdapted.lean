import tmp.sheaf.xif.paper.S2611TransportActual
import tmp.sheaf.xif.paper.S2610TTPrimeActual
import tmp.sheaf.xif.paper.S2609SSPrimeActual
import tmp.sheaf.xif.paper.S2600TIntegralClosureActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace LeanFormal.IUT.XiFPaper.S2612PhiEqLiftSTActualAdapted

open LeanFormal.IUT.XiFPaper.S2611TransportActual
open LeanFormal.IUT.XiFPaper.S2610TTPrimeActual
open LeanFormal.IUT.XiFPaper.S2609SSPrimeActual
open LeanFormal.IUT.XiFPaper.S2599TInstancesActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2600TIntegralClosureActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual

local instance hlocS : IsLocalization (LeanFormal.IUT.XiFPaper.S2609SSPrimeActual.M) Sb := by
  rw [← LeanFormal.IUT.XiFPaper.S2609SSPrimeActual.hMN]
  exact Localization.isLocalization

local instance hlocT : IsLocalization (LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.MT) T0 := by
  rw [← LeanFormal.IUT.XiFPaper.S2610TTPrimeActual.hMT]
  exact Localization.isLocalization

local instance hlocS' : IsLocalization (Submonoid.powers (Cden : Cb)) Sb := by
  change IsLocalization (Submonoid.powers ((algebraMap ℤ Cb c) : Cb)) Sb
  exact hlocS

noncomputable def eTTa : T ≃ₐ[OL] T' := IsLocalization.algEquiv MT T T'
noncomputable def eSSa : Sb ≃ₐ[Cb] S' := IsLocalization.algEquiv (LeanFormal.IUT.XiFPaper.S2609SSPrimeActual.M) Sb S'

lemma phi_eq_liftST : phi = liftST := by
  apply IsLocalization.ringHom_ext (M := Submonoid.powers (Cden : Cb))
  ext x
  simp only [phi, eSS', eTT', liftST]
  change eTTa.symm (algebraMap Cb T' x) = algebraMap OL T (algebraMap Cb OL x)
  rw [← IsScalarTower.algebraMap_apply Cb OL T']
  exact IsLocalization.algEquiv_comp_algebraMap_apply

end LeanFormal.IUT.XiFPaper.S2612PhiEqLiftSTActualAdapted
end