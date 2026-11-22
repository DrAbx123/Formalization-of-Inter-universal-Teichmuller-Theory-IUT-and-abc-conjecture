import tmp.sheaf.xif.paper.S2482QiOrbicurveActual
import tmp.sheaf.xif.paper.S2482QiInvolutionActual
import tmp.sheaf.xif.paper.S2482QiInvolutionSquareActual
import tmp.sheaf.xif.paper.S2482QiNontrivialActual
import tmp.sheaf.xif.paper.S2489FbarActual
import tmp.sheaf.xif.paper.S2490RestrictionSectionActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionSquareActual
open LeanFormal.IUT.XiFPaper.S2482QiNontrivialActual
open LeanFormal.IUT.XiFPaper.S2489FbarActual
open LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual
namespace LeanFormal.IUT.XiFPaper.S2492CorrectedFSourceBundle

structure S2482CorrectedFSourceData where
  xF : Iut.HyperbolicOrbicurve S2490A.F
  xF_geometry : SourceOncePuncturedGeometry S2490A.curve xF
  ellipticInvolution : xF.Hom xF
  ellipticInvolution_squared :
    (ellipticInvolution.comp ellipticInvolution).TwoIso (Iut.HyperbolicOrbicurve.Hom.id xF)
  ellipticInvolution_nontrivial : ellipticInvolution ≠ Iut.HyperbolicOrbicurve.Hom.id xF
  V : Set (NumberFieldPlace S2490A.K)
  V_mod_bad : Set (NumberField.FinitePlace S2490A.Fmod)
  V_mod_bad_odd_residue_characteristic :
    ∀ p ∈ V_mod_bad, Odd (NumberFieldFinitePlace.residueCharacteristic p)
  V_mod_bad_nonempty : V_mod_bad.Nonempty
  V_section : NumberFieldPlace.RestrictionSection S2490A.Fmod S2490A.K
  V_eq_section : V = V_section.selected
  V_mod_bijection : NumberFieldPlace S2490A.Fmod ≃ {v // v ∈ V}
  V_place_comap : ∀ (v : {v // v ∈ V}),
    (((v : NumberFieldPlace S2490A.K).comap : NumberFieldPlace S2490A.Fmod) =
      V_mod_bijection.symm v)
  fbar : SourceFbarExtension S2490A

def S2492Bundle : S2482CorrectedFSourceData where
  xF := S2482Orbicurve
  xF_geometry := S2482OncePuncturedGeometry
  ellipticInvolution := S2482EllipticInvolution
  ellipticInvolution_squared := S2482EllipticInvolution_square
  ellipticInvolution_nontrivial := S2482EllipticInvolution_ne_id
  V := S2490V
  V_mod_bad := S2490VModBad
  V_mod_bad_odd_residue_characteristic := S2490VModBad_odd
  V_mod_bad_nonempty := S2490VModBad_nonempty
  V_section := S2490RestrictionSection
  V_eq_section := rfl
  V_mod_bijection := S2490VModBijection
  V_place_comap := S2490VPlaceComap
  fbar := S2489Fbar S2490A

#print axioms S2492Bundle
end LeanFormal.IUT.XiFPaper.S2492CorrectedFSourceBundle
end