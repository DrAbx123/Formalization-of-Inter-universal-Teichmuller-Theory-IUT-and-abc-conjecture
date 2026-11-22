import tmp.sheaf.xif.paper.S2913ChartFactorizationAttempt
import tmp.sheaf.xif.paper.S2978ClassificationInputActual
import tmp.sheaf.xif.paper.S2897ValuationInputActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2913ChartFactorizationAttempt
open LeanFormal.IUT.XiFPaper.S2978ClassificationInputActual
open LeanFormal.IUT.XiFPaper.S2897ValuationInputActual
open LeanFormal.IUT.XiFPaper.S2888OriginPreservingOrderTwo
open LeanFormal.IUT.XiFPaper.S2902CoreWithQMinimalActual
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2889AffineOrderTwoActual
open LeanFormal.IUT.XiFPaper.S2877UniqueReductionAudit
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2990ClassificationDataConstruction

/-- Inputs for constructing the four classification-data items. -/
structure S2990Inputs where
  valuation : S2897ValuationInput
  xfixed : S2897XFixedInput valuation
  haff : S2889AffineOrderTwoClassification
  origin : ∀ β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X,
    β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X → S2888OriginPreserving β
  originToChart : S2913OriginToChart
  underlying_ne_id_iff :
    ∀ inv : LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.Hom
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve,
      S2877Underlying inv ≠ 𝟙 S2844D6F6BaseChangeActual.S2844X ↔
        inv ≠ Iut.HyperbolicOrbicurve.Hom.id
          LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve

/-- Actual chart factorization: origin-preservation plus the S2913 input. -/
noncomputable def S2990ChartData
    (I : S2990Inputs)
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (hβ : β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X) : S2890ChartData β :=
  S2913ChartData_of_factorization
    (Classical.choice (I.originToChart β hβ (I.origin β hβ)))

/-- Actual φ(X)=X from the valuation/XFixed input. -/
theorem S2990_phiX_eq
    (I : S2990Inputs)
    (φ : S2801E37CoordinateRing S2844D6F6BaseChangeActual.K ≃ₐ[S2844D6F6BaseChangeActual.K]
      S2801E37CoordinateRing S2844D6F6BaseChangeActual.K)
    (hφ2 : φ.toRingHom.comp φ.toRingHom =
      RingHom.id (S2801E37CoordinateRing S2844D6F6BaseChangeActual.K))
    (hfil : S2897FiltrationPreserving I.valuation φ) :
    φ (S2801E37X S2844D6F6BaseChangeActual.K) =
      S2801E37X S2844D6F6BaseChangeActual.K :=
  S2896XFixed_of_valuation I.valuation I.xfixed φ hφ2 hfil

/-- Actual construction of S2978MissingClassificationData: haff/origin/
underlying are the supplied actual inputs, chart factorization is constructed
from origin + S2913. -/
noncomputable def S2990MissingClassificationData
    (I : S2990Inputs) : S2978MissingClassificationData where
  haff := I.haff
  chart := fun β hβ => S2990ChartData I β hβ
  origin := I.origin
  underlying_ne_id_iff := I.underlying_ne_id_iff

/-- The construction yields S2902UniqueData. -/
noncomputable def S2990UniqueData (I : S2990Inputs) : S2902UniqueData :=
  S2978UniqueDataOfMissing (S2990MissingClassificationData I)

/-!
## First error / missing objects

Constructed actually:
* S2990ChartData: for every order-two scheme automorphism, chart factorization
  follows from the S2913 origin-to-chart input plus origin preservation.
* S2990_phiX_eq: φ(X)=X follows from the S2897 valuation and its XFixed input.
* S2990MissingClassificationData: the S2978 four-field package, with chart
  factorization constructed; haff/origin/underlying are the supplied inputs.

Still explicit:
* a proof of S2897XFixedInput for the actual valuation (valuation/degree
  theory);
* a proof of S2913OriginToChart (origin-preserving auto preserves chart Z);
* a proof of S2889AffineOrderTwoClassification (order-two affine
  classification);
* an actual origin-preservation supplier for all order-two scheme autos;
* the underlying_ne_id_iff equivalence.

No classification is faked; these five remain the exact missing inputs.
-/

#check S2990Inputs
#check S2990ChartData
#check S2990_phiX_eq
#check S2990MissingClassificationData
#check S2990UniqueData
#print axioms S2990ChartData
#print axioms S2990_phiX_eq

end LeanFormal.IUT.XiFPaper.S2990ClassificationDataConstruction
end
