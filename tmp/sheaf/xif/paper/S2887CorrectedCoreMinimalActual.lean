import tmp.sheaf.xif.paper.S2880CorrectedA6CoreNontrivialActual
import tmp.sheaf.xif.paper.S2883UniqueFromClassification
import tmp.sheaf.xif.paper.S2884GroupsInclusionActual
import tmp.sheaf.xif.paper.S2873CuspGenericActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2876CorrectedA6CoreActual
open LeanFormal.IUT.XiFPaper.S2877UniqueReductionAudit
open LeanFormal.IUT.XiFPaper.S2880CorrectedA6CoreNontrivialActual
open LeanFormal.IUT.XiFPaper.S2883UniqueFromClassification
open LeanFormal.IUT.XiFPaper.S2884GroupsInclusionActual
open LeanFormal.IUT.XiFPaper.S2873CuspGenericActual
open LeanFormal.IUT.XiFPaper.S2482CorrectedSourceSignQuotientActual
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

namespace LeanFormal.IUT.XiFPaper.S2887CorrectedCoreMinimalActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

/-- Minimal explicit inputs: unique from S2883, groups from S2884, cusp from
S2873; cF/quotient/K-side/V stay explicit. -/
structure S2887Inputs
    (signAction : Iut.OrbicurveSignAction
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve) where
  uniqueInput : S2883Inputs
  cF : Iut.HyperbolicOrbicurve S2847A6.F
  quotient : Iut.OrbicurveSignInvariantMorphism signAction cF
  quotientWitness : Iut.OrbicurveSignQuotientWitness signAction quotient
  groups : CoreGroupsInput
    LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve
    cF (Iut.AbsoluteGaloisProfinite S2847A6.F)
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
  cusp : GenericCuspData cK

/-- Build S2880Inputs from S2887Inputs: unique via S2883, groups via S2884,
epsilon via S2873. -/
noncomputable def S2887_toS2880
    (D : Pseudofunctor Iut.SignActionIndex
      (Iut.EtaleStackPseudofunctor S2847A6.F))
    (atBase : Bicategory.Equivalence (D.obj Iut.signActionObject)
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.stack.fiber)
    (generator_identification :
      (atBase.inv ≫ D.map Iut.signActionGenerator) ≫ atBase.hom ≅
        S2857StackAuto alphaOverS2844)
    (I : S2887Inputs (S2869SignAction D atBase generator_identification)) :
    S2880Inputs (S2869SignAction D atBase generator_identification) :=
  { unique_elliptic_involution := by
      intro inv hsq hnt
      exact S2883_unique I.uniqueInput inv hsq hnt
    cF := I.cF
    quotient := I.quotient
    quotientWitness := I.quotientWitness
    xFGroups := I.groups.xFGroups
    cFGroups := I.groups.cFGroups
    fGroupInclusion := I.groups.fGroupInclusion
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
    epsilon := cuspOfGenericData I.cusp }

/-- Corrected A6 core with minimal explicit data. -/
noncomputable def S2887Core
    (D : Pseudofunctor Iut.SignActionIndex
      (Iut.EtaleStackPseudofunctor S2847A6.F))
    (atBase : Bicategory.Equivalence (D.obj Iut.signActionObject)
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.stack.fiber)
    (generator_identification :
      (atBase.inv ≫ D.map Iut.signActionGenerator) ≫ atBase.hom ≅
        S2857StackAuto alphaOverS2844)
    (I : S2887Inputs (S2869SignAction D atBase generator_identification)) :
    SourceSignQuotientDataCorrected S2847A6 :=
  S2880Core D atBase generator_identification
    (S2883_toS2880 I.uniqueInput
      (S2869SignAction D atBase generator_identification)
      (S2887_toS2880 D atBase generator_identification I))

#check S2887Inputs
#check S2887_toS2880
#check S2887Core
#print axioms S2887Core

end LeanFormal.IUT.XiFPaper.S2887CorrectedCoreMinimalActual
end
