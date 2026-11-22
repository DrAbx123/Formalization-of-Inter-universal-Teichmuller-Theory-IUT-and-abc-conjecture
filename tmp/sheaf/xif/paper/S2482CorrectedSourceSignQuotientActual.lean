import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import tmp.sheaf.xif.paper.S2482QiNontrivialActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2482CorrectedSourceSignQuotientActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

universe u

/-- Corrected source sign-quotient package: the identity endomorphism is excluded
from the uniqueness statement, and nontriviality is an explicit field. -/
structure SourceSignQuotientDataCorrected
    {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l) where
  xF : Iut.HyperbolicOrbicurve A.F
  xF_geometry : SourceOncePuncturedGeometry A.curve xF
  ellipticInvolution : xF.Hom xF
  ellipticInvolution_squared :
    Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp ellipticInvolution ellipticInvolution)
      (Iut.HyperbolicOrbicurve.Hom.id xF)
  ellipticInvolution_nontrivial :
    ellipticInvolution ≠ Iut.HyperbolicOrbicurve.Hom.id xF
  unique_elliptic_involution :
    ∀ inv : xF.Hom xF,
      Iut.HyperbolicOrbicurve.Hom.TwoIso
        (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
        (Iut.HyperbolicOrbicurve.Hom.id xF) →
      inv ≠ Iut.HyperbolicOrbicurve.Hom.id xF →
      Nonempty (Iut.HyperbolicOrbicurve.Hom.TwoIso inv ellipticInvolution)
  signAction : Iut.OrbicurveSignAction xF
  signAction_inversion_eq_ellipticInvolution :
    signAction.inversion = ellipticInvolution
  cF : Iut.HyperbolicOrbicurve A.F
  quotient : Iut.OrbicurveSignInvariantMorphism signAction cF
  quotientWitness : Iut.OrbicurveSignQuotientWitness signAction quotient
  xFGroups : SourceOrbicurveGroupData xF (Iut.AbsoluteGaloisProfinite A.F)
  cFGroups : SourceOrbicurveGroupData cF (Iut.AbsoluteGaloisProfinite A.F)
  fGroupInclusion : Iut.ProfiniteFundamentalGroupInclusion
    xFGroups.sequence.geometric xFGroups.sequence.arithmetic
    cFGroups.sequence.geometric cFGroups.sequence.arithmetic
    (Iut.AbsoluteGaloisProfinite A.F)
    xFGroups.sequence cFGroups.sequence
  xK : Iut.HyperbolicOrbicurve A.K
  cK : Iut.HyperbolicOrbicurve A.K
  xKExtension : SourceOrbicurveScalarExtension A.F A.K xF
  cKExtension : SourceOrbicurveScalarExtension A.F A.K cF
  xKType : xK.signature = sourceTypeOneLTorsion l
  cKType : cK.signature = sourceTypeOneLTorsionPlusMinus l
  xK_eq_extension : xK = xKExtension.result
  cK_eq_extension : cK = cKExtension.result
  V : Set (NumberFieldPlace A.K)
  V_mod_bad : Set (NumberField.FinitePlace A.Fmod)
  V_mod_bad_odd_residue_characteristic :
    ∀ p, p ∈ V_mod_bad →
      Odd (NumberFieldFinitePlace.residueCharacteristic p)
  V_mod_bad_nonempty : V_mod_bad.Nonempty
  V_section : NumberFieldPlace.RestrictionSection A.Fmod A.K
  V_eq_section : V = V_section.selected
  V_mod_bijection :
    NumberFieldPlace A.Fmod ≃ {v : NumberFieldPlace A.K // v ∈ V}
  V_place_comap :
    ∀ v : {v : NumberFieldPlace A.K // v ∈ V},
      NumberFieldPlace.comap (k := A.Fmod) v.1 =
        (V_mod_bijection.symm v)
  epsilon : Iut.OrbicurveBoundaryCusp cK

#check SourceSignQuotientDataCorrected

end LeanFormal.IUT.XiFPaper.S2482CorrectedSourceSignQuotientActual

end