import tmp.sheaf.xif.paper.S2492CorrectedFSourceBundle
import tmp.sheaf.xif.paper.S2495cFUnconditionalActual
import tmp.sheaf.xif.paper.S2517EpsilonActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual
open LeanFormal.IUT.XiFPaper.S2492CorrectedFSourceBundle
open LeanFormal.IUT.XiFPaper.S2495cFUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2517EpsilonActual
noncomputable local instance : Field S2490A.F := inferInstance
noncomputable local instance : CommRing S2490A.F := inferInstance
noncomputable local instance : Field S2490A.K := inferInstance
noncomputable local instance : CommRing S2490A.K := inferInstance
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S2518CorrectedSourceBundle

/-- Corrected source bundle with all F-side fields actual, plus the actual
F-side quotient cF, K-side quotient cK, and the boundary cusp epsilon.
Only the group/scalar-extension data are absent. -/
structure S2518Bundle where
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
  cF : Iut.HyperbolicOrbicurve S2490A.F
  cK : Iut.HyperbolicOrbicurve S2490A.K
  epsilon : Iut.OrbicurveBoundaryCusp cK

noncomputable def S2518Actual : S2518Bundle where
  xF := S2492Bundle.xF
  xF_geometry := S2492Bundle.xF_geometry
  ellipticInvolution := S2492Bundle.ellipticInvolution
  ellipticInvolution_squared := S2492Bundle.ellipticInvolution_squared
  ellipticInvolution_nontrivial := S2492Bundle.ellipticInvolution_nontrivial
  V := S2492Bundle.V
  V_mod_bad := S2492Bundle.V_mod_bad
  V_mod_bad_odd_residue_characteristic := S2492Bundle.V_mod_bad_odd_residue_characteristic
  V_mod_bad_nonempty := S2492Bundle.V_mod_bad_nonempty
  V_section := S2492Bundle.V_section
  V_eq_section := S2492Bundle.V_eq_section
  V_mod_bijection := S2492Bundle.V_mod_bijection
  V_place_comap := S2492Bundle.V_place_comap
  fbar := S2492Bundle.fbar
  cF := S2495cF
  cK := S2495cK
  epsilon := S2517Epsilon

#check S2518Actual
#print axioms S2518Actual
end LeanFormal.IUT.XiFPaper.S2518CorrectedSourceBundle
end