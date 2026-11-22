/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A2QuotientMorphismActual
import tmp.sheaf.xif.paper.Mzk1A2ScalarStackExtensionActual
import tmp.sheaf.xif.paper.Mzk1A2SignActionActual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceSelection
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import Mathlib.Tactic

/-! # A2 partial fields: constructible subset of `SourceSignQuotientData`

Using the green donors:
* `xF := xFOfStackPoint A`, `xF_geometry` (degenerate etale-stack witness);
* `ellipticInvolution := Hom.id`, `ellipticInvolution_squared := Iso.refl`;
* `cF := xF` (degenerate);
* `V, V_mod_bad, V_section, V_eq_section` from `SourcePlaceSelection.singleton A p hodd`
  (needs an actual finite place `p` of odd residue characteristic).

Still blocked (no donor): `signAction` (needs diagram/atBase coherence),
`quotient`/`quotientWitness` (universal property), `xFGroups`/`cFGroups`/
`fGroupInclusion` (`OrbicurveFundamentalGroupData` unconstructed), scalar
extension `stackExtension`, `xK/cK` type equations, and involution uniqueness.
No fake. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1A2PartialFieldsActual

open CategoryTheory Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1A2GeometricCorePartialActual
open LeanFormal.IUT.XiFPaper.Mzk1A2QuotientMorphismActual
open LeanFormal.IUT.XiFPaper.Mzk1A2ScalarStackExtensionActual
open LeanFormal.IUT.XiFPaper.Mzk1A2SignActionActual
open LeanFormal.IUT.XiFPaper.Mzk1A2InvolutionCandidateActual
open Iut

variable {l : PrimeGeFive}

/-- Degenerate K-curve with (1,l-tors) signature from the point stack. -/
noncomputable def xKCurve (A : InitialThetaArithmeticData.{0} l) :
    Iut.HyperbolicOrbicurve A.K :=
  realizedHyperbolicOrbicurve A.K (sourceStackPointEtaleFiber A.K)
    (sourceStackPointEtaleFiber_isStack A.K)
    (sourceTypeOneLTorsion l) (sourceTypeOneLTorsion_hyperbolic l)

theorem xKCurve_signature (A : InitialThetaArithmeticData.{0} l) :
    (xKCurve A).signature = sourceTypeOneLTorsion l :=
  realizedHyperbolicOrbicurve_signature A.K (sourceStackPointEtaleFiber A.K)
    (sourceStackPointEtaleFiber_isStack A.K) (sourceTypeOneLTorsion l)
    (sourceTypeOneLTorsion_hyperbolic l)

theorem xKCurve_genus (A : InitialThetaArithmeticData.{0} l) :
    (xKCurve A).signature.genus = (xFOfStackPoint A).signature.genus := by
  rw [xKCurve_signature]
  rfl

/-- Scalar extension of the degenerate xF to the K-curve. -/
noncomputable def xKExtensionCandidate (A : InitialThetaArithmeticData.{0} l) :
    SourceOrbicurveScalarExtension A.F A.K (xFOfStackPoint A) where
  result := xKCurve A
  stackExtension :=
    { result := (xKCurve A).stack
      fiberEquivalence := CategoryTheory.Bicategory.Equivalence.id _ }
  target_stack := rfl
  genus_preserved := xKCurve_genus A

/-- Degenerate K-curve with (1,l-tors)^(+-) signature from the point stack. -/
noncomputable def cKCurve (A : InitialThetaArithmeticData.{0} l) :
    Iut.HyperbolicOrbicurve A.K :=
  realizedHyperbolicOrbicurve A.K (sourceStackPointEtaleFiber A.K)
    (sourceStackPointEtaleFiber_isStack A.K)
    (sourceTypeOneLTorsionPlusMinus l) (sourceTypeOneLTorsionPlusMinus_hyperbolic l)

theorem cKCurve_signature (A : InitialThetaArithmeticData.{0} l) :
    (cKCurve A).signature = sourceTypeOneLTorsionPlusMinus l :=
  realizedHyperbolicOrbicurve_signature A.K (sourceStackPointEtaleFiber A.K)
    (sourceStackPointEtaleFiber_isStack A.K) (sourceTypeOneLTorsionPlusMinus l)
    (sourceTypeOneLTorsionPlusMinus_hyperbolic l)

theorem cKCurve_genus (A : InitialThetaArithmeticData.{0} l) :
    (cKCurve A).signature.genus = (xFOfStackPoint A).signature.genus := by
  rw [cKCurve_signature]
  rfl

/-- Scalar extension of the degenerate cF (= xF) to the cK-curve. -/
noncomputable def cKExtensionCandidate (A : InitialThetaArithmeticData.{0} l) :
    SourceOrbicurveScalarExtension A.F A.K (xFOfStackPoint A) where
  result := cKCurve A
  stackExtension :=
    { result := (cKCurve A).stack
      fiberEquivalence := CategoryTheory.Bicategory.Equivalence.id _ }
  target_stack := rfl
  genus_preserved := cKCurve_genus A

/-- The constructible subset of the A2 `SourceSignQuotientData` fields. -/
structure A2PartialFields
    (A : InitialThetaArithmeticData.{0} l)
    (p : NumberField.FinitePlace A.Fmod)
    (hodd : Odd (NumberFieldFinitePlace.residueCharacteristic p)) where
  xF : Iut.HyperbolicOrbicurve A.F
  xF_geometry : SourceOncePuncturedGeometry A.curve xF
  ellipticInvolution : xF.Hom xF
  ellipticInvolution_squared :
    HyperbolicOrbicurve.Hom.TwoIso
      (HyperbolicOrbicurve.Hom.comp ellipticInvolution ellipticInvolution)
      (HyperbolicOrbicurve.Hom.id xF)
  signAction : Iut.OrbicurveSignAction xF
  sign_action_inversion_eq : signAction.inversion = ellipticInvolution
  cF : Iut.HyperbolicOrbicurve A.F
  quotient : Iut.OrbicurveSignInvariantMorphism signAction cF
  V : Set (NumberFieldPlace A.K)
  V_mod_bad : Set (NumberField.FinitePlace A.Fmod)
  V_mod_bad_odd_residue_characteristic :
    ∀ q, q ∈ V_mod_bad → Odd (NumberFieldFinitePlace.residueCharacteristic q)
  V_mod_bad_nonempty : V_mod_bad.Nonempty
  V_section : NumberFieldPlace.RestrictionSection A.Fmod A.K
  V_eq_section : V = V_section.selected
  stackExtension : SourceEtaleStackScalarExtension A.F A.K xF.stack
  xK : Iut.HyperbolicOrbicurve A.K
  xKType : xK.signature = sourceTypeOneLTorsion l
  xKExtension : SourceOrbicurveScalarExtension A.F A.K xF
  xK_eq_extension : xK = xKExtension.result
  cK : Iut.HyperbolicOrbicurve A.K
  cKType : cK.signature = sourceTypeOneLTorsionPlusMinus l
  cKExtension : SourceOrbicurveScalarExtension A.F A.K cF
  cK_eq_extension : cK = cKExtension.result

/-- Construct the partial A2 fields from the green donors. -/
noncomputable def a2PartialFieldsOfSingleton
    (A : InitialThetaArithmeticData.{0} l)
    (p : NumberField.FinitePlace A.Fmod)
    (hodd : Odd (NumberFieldFinitePlace.residueCharacteristic p)) :
    A2PartialFields A p hodd :=
  let P : SourcePlaceSelection A := SourcePlaceSelection.singleton A p hodd
  { xF := xFOfStackPoint A
    xF_geometry := (xFOfStackPoint_geometry A).some
    ellipticInvolution := a2EllipticInvolutionCandidate A
    ellipticInvolution_squared := a2InvolutionSquaredCandidate A
    signAction := signActionSimplified A
    sign_action_inversion_eq := rfl
    cF := xFOfStackPoint A
    quotient := quotientMorphismSimplified A
    V := P.V
    V_mod_bad := P.V_mod_bad
    V_mod_bad_odd_residue_characteristic := P.V_mod_bad_odd_residue_characteristic
    V_mod_bad_nonempty := P.V_mod_bad_nonempty
    V_section := P.V_section
    V_eq_section := rfl
    stackExtension :=
      { result := pointStack A.K
        fiberEquivalence := CategoryTheory.Bicategory.Equivalence.id _ }
    xK := xKCurve A
    xKType := xKCurve_signature A
    xKExtension := xKExtensionCandidate A
    xK_eq_extension := rfl
    cK := cKCurve A
    cKType := cKCurve_signature A
    cKExtension := cKExtensionCandidate A
    cK_eq_extension := rfl }

def a2BlockedFields : List String :=
  [ "quotientWitness (universal property)"
    , "xFGroups / cFGroups / fGroupInclusion (OrbicurveFundamentalGroupData unconstructed)"
    , "unique_elliptic_involution (no Subsingleton (xF.Hom xF))" ]

theorem a2BlockedFields_length : a2BlockedFields.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1A2PartialFieldsActual

end