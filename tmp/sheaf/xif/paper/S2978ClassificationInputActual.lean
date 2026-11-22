import tmp.sheaf.xif.paper.S2902CoreWithQMinimalActual
import tmp.sheaf.xif.paper.S2883UniqueFromClassification

noncomputable section
open LeanFormal.IUT
open CategoryTheory
open LeanFormal.IUT.XiFPaper.S2902CoreWithQMinimalActual
open LeanFormal.IUT.XiFPaper.S2883UniqueFromClassification
open LeanFormal.IUT.XiFPaper.S2889AffineOrderTwoActual
open LeanFormal.IUT.XiFPaper.S2888OriginPreservingOrderTwo
open LeanFormal.IUT.XiFPaper.S2877UniqueReductionAudit
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2978ClassificationInputActual

/-- Actual wrapper: S2902UniqueData is exactly the classification/origin data
needed by S2883Inputs. -/
noncomputable def S2978ClassificationInput
    (U : S2902UniqueData) : S2883Inputs :=
  S2902_toS2883 U

/-- The classification field extracted from the actual wrapper. -/
theorem S2978_classification (U : S2902UniqueData) :
    (S2978ClassificationInput U).classification =
      (S2902_toS2883 U).classification := rfl

/-- The origin/nontriviality field extracted from the actual wrapper. -/
theorem S2978_underlying_ne_id_iff (U : S2902UniqueData) :
    (S2978ClassificationInput U).underlying_ne_id_iff =
      (S2902_toS2883 U).underlying_ne_id_iff := rfl

/-- Feed the classification input into S2883's unique theorem. -/
theorem S2978_unique_of_input
    (U : S2902UniqueData)
    (inv : LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.Hom
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve)
    (hsq : Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
      (Iut.HyperbolicOrbicurve.Hom.id
        LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve))
    (hnt : inv ≠ Iut.HyperbolicOrbicurve.Hom.id
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve) :
    Nonempty (Iut.HyperbolicOrbicurve.Hom.TwoIso inv
      (LeanFormal.IUT.XiFPaper.S2857StackAutoForA6Actual.S2857StackAuto
        LeanFormal.IUT.XiFPaper.S2858AlphaOverActual.alphaOverS2844)) :=
  S2883_unique (S2978ClassificationInput U) inv hsq hnt

/-- Exact missing object: the four fields of S2902UniqueData, namely the affine
classification, the chart factorization for every order-two scheme
automorphism, the origin-preservation supplier, and the underlying
nontriviality equivalence. -/
structure S2978MissingClassificationData : Type where
  haff : S2889AffineOrderTwoClassification
  chart : ∀ (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X),
    β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X → S2890ChartData β
  origin : ∀ (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X),
    β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X →
      LeanFormal.IUT.XiFPaper.S2888OriginPreservingOrderTwo.S2888OriginPreserving β
  underlying_ne_id_iff :
    ∀ (inv : LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.Hom
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve),
      LeanFormal.IUT.XiFPaper.S2877UniqueReductionAudit.S2877Underlying inv ≠
        𝟙 S2844D6F6BaseChangeActual.S2844X ↔
        inv ≠ Iut.HyperbolicOrbicurve.Hom.id
          LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve

/-- Actual S2902UniqueData from the missing classification data. -/
noncomputable def S2978UniqueDataOfMissing
    (M : S2978MissingClassificationData) : S2902UniqueData where
  haff := M.haff
  chart := M.chart
  origin := M.origin
  underlying_ne_id_iff := M.underlying_ne_id_iff

#check S2978ClassificationInput
#check S2978_classification
#check S2978_underlying_ne_id_iff
#check S2978_unique_of_input
#check S2978MissingClassificationData
#check S2978UniqueDataOfMissing
#print axioms S2978ClassificationInput

end LeanFormal.IUT.XiFPaper.S2978ClassificationInputActual
end
