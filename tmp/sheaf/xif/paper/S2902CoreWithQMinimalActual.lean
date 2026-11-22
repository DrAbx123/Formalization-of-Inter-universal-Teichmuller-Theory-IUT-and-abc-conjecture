import tmp.sheaf.xif.paper.S2892CoreWithQActual
import tmp.sheaf.xif.paper.S2890ClassificationConditionalActual
import tmp.sheaf.xif.paper.S2897ValuationInputActual
import tmp.sheaf.xif.paper.S2895KSideInputActual
import tmp.sheaf.xif.paper.S2894CuspFiveFieldsActual
import tmp.sheaf.xif.paper.S2882A6PointwisePseudofunctorActual
import tmp.sheaf.xif.paper.S2870A6CFPathAudit
import tmp.sheaf.xif.paper.S2853E37NegationAutomorphismActual
import tmp.sheaf.xif.paper.S2482CorrectedSourceSignQuotientActual
import tmp.sheaf.xif.paper.S2901CuspBoundaryInputActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2892CoreWithQActual
open LeanFormal.IUT.XiFPaper.S2890ClassificationConditionalActual
open LeanFormal.IUT.XiFPaper.S2897ValuationInputActual
open LeanFormal.IUT.XiFPaper.S2895KSideInputActual
open LeanFormal.IUT.XiFPaper.S2894CuspFiveFieldsActual
open LeanFormal.IUT.XiFPaper.S2887CorrectedCoreMinimalActual
open LeanFormal.IUT.XiFPaper.S2883UniqueFromClassification
open LeanFormal.IUT.XiFPaper.S2884GroupsInclusionActual
open LeanFormal.IUT.XiFPaper.S2889AffineOrderTwoActual
open LeanFormal.IUT.XiFPaper.S2891A6CFActual
open LeanFormal.IUT.XiFPaper.S2873CuspGenericActual
open LeanFormal.IUT.XiFPaper.S2869A6CoreWithGenericQuotient
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2857StackAutoForA6Actual
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2870A6CFPathAudit
open LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual
open LeanFormal.IUT.XiFPaper.S2482CorrectedSourceSignQuotientActual
open LeanFormal.IUT.XiFPaper.S2901CuspBoundaryInputActual
open scoped Pseudofunctor.StrongTrans
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2902CoreWithQMinimalActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

/-- Chart-factorization data for one order-two scheme automorphism, as used by
S2890_classification_of_affine. -/
structure S2890ChartData
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X) where
  z : S2801E37AffineScheme S2844D6F6BaseChangeActual.K ⟶
    S2801E37AffineScheme S2844D6F6BaseChangeActual.K
  φ : S2801E37CoordinateRing S2844D6F6BaseChangeActual.K ≃ₐ[S2844D6F6BaseChangeActual.K]
    S2801E37CoordinateRing S2844D6F6BaseChangeActual.K
  hz : z = Spec.map (CommRingCat.ofHom φ.toRingHom)
  hφsq : φ.toRingHom.comp φ.toRingHom =
    RingHom.id (S2801E37CoordinateRing S2844D6F6BaseChangeActual.K)
  hZ : S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ β.left =
    z ≫ S2820E37ChartZMap S2844D6F6BaseChangeActual.K
  hZalpha : S2853ChartZSchemeEndo S2844D6F6BaseChangeActual.K ≫
      S2820E37ChartZMap S2844D6F6BaseChangeActual.K =
    S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ alphaOverS2844.left
  hY : S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫ β.left =
    S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫ alphaOverS2844.left
  hYid : S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫ β.left =
    S2820E37ChartYMap S2844D6F6BaseChangeActual.K
  hoverlap : z = S2853ChartZSchemeEndo S2844D6F6BaseChangeActual.K
  hglue : ∀ γ : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X,
    S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ γ.left =
      S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ β.left →
    S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫ γ.left =
      S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫ β.left →
    γ = β

/-- Conditional unique data: affine classification + chart factorization +
origin-preservation supplier + underlying nontriviality equivalence. -/
structure S2902UniqueData where
  haff : S2889AffineOrderTwoClassification
  chart : ∀ β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X,
    β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X → S2890ChartData β
  origin : ∀ β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X,
    β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X →
      LeanFormal.IUT.XiFPaper.S2888OriginPreservingOrderTwo.S2888OriginPreserving β
  underlying_ne_id_iff :
    ∀ inv : S2855HyperbolicOrbicurve.Hom S2855HyperbolicOrbicurve,
      LeanFormal.IUT.XiFPaper.S2877UniqueReductionAudit.S2877Underlying inv ≠
        𝟙 S2844D6F6BaseChangeActual.S2844X ↔
        inv ≠ Iut.HyperbolicOrbicurve.Hom.id S2855HyperbolicOrbicurve

/-- Convert the conditional data to S2883Inputs. -/
noncomputable def S2902_toS2883 (U : S2902UniqueData) : S2883Inputs where
  classification := by
    intro β hβ
    obtain ⟨z, φ, hz, hφsq, hZ, hZalpha, hY, hYid, hoverlap, hglue⟩ := U.chart β hβ
    exact S2890_classification_of_affine U.haff β hβ (U.origin β hβ)
      z φ hz hφsq hZ hZalpha hY hYid hoverlap hglue
  underlying_ne_id_iff := U.underlying_ne_id_iff

/-- Minimal S2902 inputs. -/
structure S2902Inputs
    (hQ : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology S2844D6F6BaseChangeActual.K))
    (A : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve)
    (W : S2870QuotientWitnessData S2882A6Q hQ A) where
  uniqueData : S2902UniqueData
  groups : CoreGroupsInput S2855HyperbolicOrbicurve (S2891CF hQ)
    (Iut.AbsoluteGaloisProfinite S2847A6.F)
  kSide : S2895KInput S2855HyperbolicOrbicurve (S2891CF hQ)
  xKType : kSide.xK.signature = sourceTypeOneLTorsion S2771FiveLabel
  cKType : kSide.cK.signature = sourceTypeOneLTorsionPlusMinus S2771FiveLabel
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
  cusp : S2901CuspInput kSide.cK

/-- Build S2892Inputs from S2902Inputs. -/
noncomputable def S2902_toS2892
    (hQ : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology S2844D6F6BaseChangeActual.K))
    (D : Pseudofunctor Iut.SignActionIndex
      (Iut.EtaleStackPseudofunctor S2847A6.F))
    (atBase : Bicategory.Equivalence (D.obj Iut.signActionObject)
      S2855HyperbolicOrbicurve.stack.fiber)
    (generator_identification :
      (atBase.inv ≫ D.map Iut.signActionGenerator) ≫ atBase.hom ≅
        S2857StackAuto alphaOverS2844)
    (W : S2870QuotientWitnessData S2882A6Q hQ
      (S2869SignAction D atBase generator_identification))
    (I : S2902Inputs hQ
      (S2869SignAction D atBase generator_identification) W) :
    S2892Inputs hQ
      (S2869SignAction D atBase generator_identification) W :=
  { uniqueInput := S2902_toS2883 I.uniqueData
    groups := I.groups
    xK := I.kSide.xK
    cK := I.kSide.cK
    xKExtension := I.kSide.xKExtension
    cKExtension := I.kSide.cKExtension
    xKType := I.xKType
    cKType := I.cKType
    xK_eq_extension := S2895KInput.xK_eq_extension I.kSide
    cK_eq_extension := S2895KInput.cK_eq_extension I.kSide
    V := I.V
    V_mod_bad := I.V_mod_bad
    V_mod_bad_odd_residue_characteristic := I.V_mod_bad_odd_residue_characteristic
    V_mod_bad_nonempty := I.V_mod_bad_nonempty
    V_section := I.V_section
    V_eq_section := I.V_eq_section
    V_mod_bijection := I.V_mod_bijection
    V_place_comap := I.V_place_comap
    cusp := I.cusp.toGenericCuspData }

/-- S2902 core, via S2892Core. -/
noncomputable def S2902Core
    (hQ : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology S2844D6F6BaseChangeActual.K))
    (D : Pseudofunctor Iut.SignActionIndex
      (Iut.EtaleStackPseudofunctor S2847A6.F))
    (atBase : Bicategory.Equivalence (D.obj Iut.signActionObject)
      S2855HyperbolicOrbicurve.stack.fiber)
    (generator_identification :
      (atBase.inv ≫ D.map Iut.signActionGenerator) ≫ atBase.hom ≅
        S2857StackAuto alphaOverS2844)
    (W : S2870QuotientWitnessData S2882A6Q hQ
      (S2869SignAction D atBase generator_identification))
    (I : S2902Inputs hQ
      (S2869SignAction D atBase generator_identification) W) :
    SourceSignQuotientDataCorrected S2847A6 :=
  S2892Core hQ D atBase generator_identification W
    (S2902_toS2892 hQ D atBase generator_identification W I)

#check S2890ChartData
#check S2902UniqueData
#check S2902Inputs
#check S2902_toS2892
#check S2902Core
#print axioms S2902Core

end LeanFormal.IUT.XiFPaper.S2902CoreWithQMinimalActual
end
