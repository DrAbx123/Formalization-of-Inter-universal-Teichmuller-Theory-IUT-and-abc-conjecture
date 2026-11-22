import tmp.sheaf.xif.paper.S2887CorrectedCoreMinimalActual
import tmp.sheaf.xif.paper.S2901CuspBoundaryInputActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2876CorrectedA6CoreActual
open LeanFormal.IUT.XiFPaper.S2883UniqueFromClassification
open LeanFormal.IUT.XiFPaper.S2884GroupsInclusionActual
open LeanFormal.IUT.XiFPaper.S2887CorrectedCoreMinimalActual
open LeanFormal.IUT.XiFPaper.S2901CuspBoundaryInputActual
open LeanFormal.IUT.XiFPaper.S2894CuspFiveFieldsActual
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

namespace LeanFormal.IUT.XiFPaper.S2904CuspIntegrationActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

/-- S2887Inputs with `cusp : GenericCuspData cK` replaced by `S2901CuspInput cK`. -/
structure S2904Inputs
    (signAction : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve) where
  uniqueInput : S2883Inputs
  cF : Iut.HyperbolicOrbicurve S2847A6.F
  quotient : Iut.OrbicurveSignInvariantMorphism signAction cF
  quotientWitness : Iut.OrbicurveSignQuotientWitness signAction quotient
  groups : CoreGroupsInput S2855HyperbolicOrbicurve cF
    (Iut.AbsoluteGaloisProfinite S2847A6.F)
  xK : Iut.HyperbolicOrbicurve S2847A6.K
  cK : Iut.HyperbolicOrbicurve S2847A6.K
  xKExtension : SourceOrbicurveScalarExtension S2847A6.F S2847A6.K
    S2855HyperbolicOrbicurve
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
  cusp : S2901CuspInput cK

noncomputable def S2904_toS2887
    (D : Pseudofunctor Iut.SignActionIndex
      (Iut.EtaleStackPseudofunctor S2847A6.F))
    (atBase : Bicategory.Equivalence (D.obj Iut.signActionObject)
      S2855HyperbolicOrbicurve.stack.fiber)
    (generator_identification :
      (atBase.inv ≫ D.map Iut.signActionGenerator) ≫ atBase.hom ≅
        S2857StackAuto alphaOverS2844)
    (I : S2904Inputs (S2869SignAction D atBase generator_identification)) :
    S2887Inputs (S2869SignAction D atBase generator_identification) where
  uniqueInput := I.uniqueInput
  cF := I.cF
  quotient := I.quotient
  quotientWitness := I.quotientWitness
  groups := I.groups
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
  cusp := I.cusp.toGenericCuspData

noncomputable def S2904Core
    (D : Pseudofunctor Iut.SignActionIndex
      (Iut.EtaleStackPseudofunctor S2847A6.F))
    (atBase : Bicategory.Equivalence (D.obj Iut.signActionObject)
      S2855HyperbolicOrbicurve.stack.fiber)
    (generator_identification :
      (atBase.inv ≫ D.map Iut.signActionGenerator) ≫ atBase.hom ≅
        S2857StackAuto alphaOverS2844)
    (I : S2904Inputs (S2869SignAction D atBase generator_identification)) :
    SourceSignQuotientDataCorrected S2847A6 :=
  S2887Core D atBase generator_identification
    (S2904_toS2887 D atBase generator_identification I)

#check S2904Inputs
#check S2904_toS2887
#check S2904Core
#print axioms S2904Core

end LeanFormal.IUT.XiFPaper.S2904CuspIntegrationActual
end
