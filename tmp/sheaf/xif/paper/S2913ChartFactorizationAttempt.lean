import tmp.sheaf.xif.paper.S2902CoreWithQMinimalActual
import tmp.sheaf.xif.paper.S2888OriginPreservingOrderTwo

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2902CoreWithQMinimalActual
open LeanFormal.IUT.XiFPaper.S2888OriginPreservingOrderTwo
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2913ChartFactorizationAttempt

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

/-- The precise chart-factorization input needed to build S2890ChartData. -/
structure S2913ChartFactorization
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

noncomputable def S2913ChartData_of_factorization
    {β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X}
    (F : S2913ChartFactorization β) : S2890ChartData β where
  z := F.z
  φ := F.φ
  hz := F.hz
  hφsq := F.hφsq
  hZ := F.hZ
  hZalpha := F.hZalpha
  hY := F.hY
  hYid := F.hYid
  hoverlap := F.hoverlap
  hglue := F.hglue

/-- The exact unproved step: origin-preservation alone must give chart factorization. -/
def S2913OriginToChart : Prop :=
  ∀ (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X),
    β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X →
    S2888OriginPreserving β →
    Nonempty (S2913ChartFactorization β)

#check S2913ChartFactorization
#check S2913ChartData_of_factorization
#check S2913OriginToChart
#print axioms S2913ChartData_of_factorization

end LeanFormal.IUT.XiFPaper.S2913ChartFactorizationAttempt
end
