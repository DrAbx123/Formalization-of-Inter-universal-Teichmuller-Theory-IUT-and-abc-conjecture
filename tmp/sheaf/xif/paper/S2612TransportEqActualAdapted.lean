import tmp.sheaf.xif.paper.S2611TransportActual

noncomputable section
set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

namespace LeanFormal.IUT.XiFPaper.S2612TransportEqActualAdapted

open LeanFormal.IUT.XiFPaper.S2611TransportActual
open LeanFormal.IUT.XiFPaper.S2609SSPrimeActual
open LeanFormal.IUT.XiFPaper.S2610TTPrimeActual
open LeanFormal.IUT.XiFPaper.S2599TInstancesActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual

/-- The AlgEquiv underlying eSS'. -/
noncomputable def eSSa : Sb ≃ₐ[Cb] S' :=
  IsLocalization.algEquiv M Sb S'

/-- The AlgEquiv underlying eTT'. -/
noncomputable def eTTa : T ≃ₐ[OL] T' :=
  IsLocalization.algEquiv MT T T'

theorem phi_eq_liftST : phi = liftST := by
  apply IsLocalization.ringHom_ext (M := M)
  ext x
  change eTT'.symm ((algebraMap S' T') (eSS'.toRingHom (algebraMap Cb Sb x))) =
    (algebraMap OL T) (algebraMap Cb OL x)
  rw [show eSS'.toRingHom (algebraMap Cb Sb x) = algebraMap Cb S' x from
    (IsLocalization.algEquiv_comp_algebraMap_apply (eSSa) x)]
  rw [show (algebraMap S' T') (algebraMap Cb S' x) = algebraMap Cb T' x from
    (IsScalarTower.algebraMap_apply Cb S' T' x).symm]
  rw [show (algebraMap Cb T') x = (algebraMap OL T') (algebraMap Cb OL x) from
    (IsScalarTower.algebraMap_apply Cb OL T' x)]
  change eTTa.symm ((algebraMap OL T') (algebraMap Cb OL x)) =
    (algebraMap OL T) (algebraMap Cb OL x)
  exact IsLocalization.algEquiv_comp_algebraMap_apply (eTTa) (algebraMap Cb OL x)

end LeanFormal.IUT.XiFPaper.S2612TransportEqActualAdapted
