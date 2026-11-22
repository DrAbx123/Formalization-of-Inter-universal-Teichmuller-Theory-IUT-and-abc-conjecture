import tmp.sheaf.xif.paper.S2876CorrectedA6CoreActual
import tmp.sheaf.xif.paper.S2879NontrivialStackAutoActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2482CorrectedSourceSignQuotientActual
open LeanFormal.IUT.XiFPaper.S2876CorrectedA6CoreActual
open LeanFormal.IUT.XiFPaper.S2879NontrivialStackAutoActual
open LeanFormal.IUT.XiFPaper.S2869A6CoreWithGenericQuotient
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2857StackAutoForA6Actual
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2880CorrectedA6CoreNontrivialActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

structure S2880Inputs
    (signAction : Iut.OrbicurveSignAction
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve) where
  unique_elliptic_involution :
    ∀ inv : LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.Hom
        LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve,
      Iut.HyperbolicOrbicurve.Hom.TwoIso
        (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
        (Iut.HyperbolicOrbicurve.Hom.id
          LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve) →
      inv ≠ Iut.HyperbolicOrbicurve.Hom.id
        LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve →
      Nonempty (Iut.HyperbolicOrbicurve.Hom.TwoIso inv (S2857StackAuto alphaOverS2844))
  cF : Iut.HyperbolicOrbicurve S2847A6.F
  quotient : Iut.OrbicurveSignInvariantMorphism signAction cF
  quotientWitness : Iut.OrbicurveSignQuotientWitness signAction quotient
  xFGroups : SourceOrbicurveGroupData
    LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve
    (Iut.AbsoluteGaloisProfinite S2847A6.F)
  cFGroups : SourceOrbicurveGroupData cF
    (Iut.AbsoluteGaloisProfinite S2847A6.F)
  fGroupInclusion : Iut.ProfiniteFundamentalGroupInclusion
    xFGroups.sequence.geometric xFGroups.sequence.arithmetic
    cFGroups.sequence.geometric cFGroups.sequence.arithmetic
    (Iut.AbsoluteGaloisProfinite S2847A6.F) xFGroups.sequence cFGroups.sequence
  xK : Iut.HyperbolicOrbicurve S2847A6.K
  cK : Iut.HyperbolicOrbicurve S2847A6.K
  xKExtension : SourceOrbicurveScalarExtension S2847A6.F S2847A6.K
    LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve
  cKExtension : SourceOrbicurveScalarExtension S2847A6.F S2847A6.K cF
  xKType : xK.signature = sourceTypeOneLTorsion S2771FiveLabel
  cKType : cK.signature = sourceTypeOneLTorsionPlusMinus S2771FiveLabel
  xK_eq_extension : xK = xKExtension.result
  cK_eq_extension : cK = cKExtension.result
  V : Set (NumberFieldPlace S2847A6.K)
  V_mod_bad : Set (NumberField.FinitePlace S2847A6.Fmod)
  V_mod_bad_odd_residue_characteristic :
    ∀ p, p ∈ V_mod_bad →
      Odd (NumberFieldFinitePlace.residueCharacteristic p)
  V_mod_bad_nonempty : V_mod_bad.Nonempty
  V_section : NumberFieldPlace.RestrictionSection S2847A6.Fmod S2847A6.K
  V_eq_section : V = V_section.selected
  V_mod_bijection :
    NumberFieldPlace S2847A6.Fmod ≃ {v : NumberFieldPlace S2847A6.K // v ∈ V}
  V_place_comap :
    ∀ v : {v : NumberFieldPlace S2847A6.K // v ∈ V},
      NumberFieldPlace.comap (k := S2847A6.Fmod) v.1 =
        (V_mod_bijection.symm v)
  epsilon : Iut.OrbicurveBoundaryCusp cK



/-- Corrected A6 core with actual nontrivial involution. -/
noncomputable def S2880Core
    (D : Pseudofunctor Iut.SignActionIndex
      (Iut.EtaleStackPseudofunctor S2847A6.F))
    (atBase : Bicategory.Equivalence (D.obj Iut.signActionObject)
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.stack.fiber)
    (generator_identification :
      (atBase.inv ≫ D.map Iut.signActionGenerator) ≫ atBase.hom ≅
        S2857StackAuto alphaOverS2844)
    (I : S2880Inputs (S2869SignAction D atBase generator_identification)) :
    SourceSignQuotientDataCorrected S2847A6 :=
  S2876CorrectedCore D atBase generator_identification
    { ellipticInvolution_nontrivial := S2879_nontrivial
      unique_elliptic_involution := I.unique_elliptic_involution
      cF := I.cF
      quotient := I.quotient
      quotientWitness := I.quotientWitness
      xFGroups := I.xFGroups
      cFGroups := I.cFGroups
      fGroupInclusion := I.fGroupInclusion
      xK := I.xK
      cK := I.cK
      xKExtension := I.xKExtension
      cKExtension := I.cKExtension
      xKType := I.xKType
      cKType := I.cKType
      xK_eq_extension := I.xK_eq_extension
      cK_eq_extension := I.cK_eq_extension
      V := I.V
      V_mod_bad := I.V_mod_bad
      V_mod_bad_odd_residue_characteristic := I.V_mod_bad_odd_residue_characteristic
      V_mod_bad_nonempty := I.V_mod_bad_nonempty
      V_section := I.V_section
      V_eq_section := I.V_eq_section
      V_mod_bijection := I.V_mod_bijection
      V_place_comap := I.V_place_comap
      epsilon := I.epsilon }

#check S2880Inputs
#check S2880Core
#print axioms S2880Core

end LeanFormal.IUT.XiFPaper.S2880CorrectedA6CoreNontrivialActual
end
