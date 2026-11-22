import tmp.sheaf.xif.paper.S2889AffineOrderTwoActual
import tmp.sheaf.xif.paper.S2888OriginPreservingOrderTwo

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2889AffineOrderTwoActual
open LeanFormal.IUT.XiFPaper.S2888OriginPreservingOrderTwo
open LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2858AlphaSquareActual
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2890ClassificationConditionalActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

/-- Conditional classification: from the affine order-two classification plus
chart factorizations and gluing uniqueness, an order-two origin-preserving
scheme automorphism is the identity or alpha. -/
theorem S2890_classification_of_affine
    (haff : S2889AffineOrderTwoClassification)
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (hβ : β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X)
    (horg : S2888OriginPreserving β)
    (z : S2801E37AffineScheme S2844D6F6BaseChangeActual.K ⟶
      S2801E37AffineScheme S2844D6F6BaseChangeActual.K)
    (φ : S2801E37CoordinateRing S2844D6F6BaseChangeActual.K ≃ₐ[S2844D6F6BaseChangeActual.K]
      S2801E37CoordinateRing S2844D6F6BaseChangeActual.K)
    (hz : z = Spec.map (CommRingCat.ofHom φ.toRingHom))
    (hφsq : φ.toRingHom.comp φ.toRingHom =
      RingHom.id (S2801E37CoordinateRing S2844D6F6BaseChangeActual.K))
    (hZ : S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ β.left =
      z ≫ S2820E37ChartZMap S2844D6F6BaseChangeActual.K)
    (hZalpha : S2853ChartZSchemeEndo S2844D6F6BaseChangeActual.K ≫
        S2820E37ChartZMap S2844D6F6BaseChangeActual.K =
      S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ alphaOverS2844.left)
    (hY : S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫ β.left =
      S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫ alphaOverS2844.left)
    (hYid : S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫ β.left =
      S2820E37ChartYMap S2844D6F6BaseChangeActual.K)
    (hoverlap : z = S2853ChartZSchemeEndo S2844D6F6BaseChangeActual.K)
    (hglue : ∀ γ : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X,
      S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ γ.left =
        S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ β.left →
      S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫ γ.left =
        S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫ β.left →
      γ = β) :
    β = 𝟙 S2844D6F6BaseChangeActual.S2844X ∨ β = alphaOverS2844 := by
  haveI : IsOpenImmersion (S2820E37ChartZMap S2844D6F6BaseChangeActual.K) :=
    (E37ProjGlueData S2844D6F6BaseChangeActual.K
      (S2820E37TransitionIso S2844D6F6BaseChangeActual.K)).ι_isOpenImmersion
      (ULift.up false)
  haveI : Mono (S2820E37ChartZMap S2844D6F6BaseChangeActual.K) :=
    IsOpenImmersion.mono _
  rcases haff φ hφsq with hφ | hφ
  · left
    have hzid : z = 𝟙 (S2801E37AffineScheme S2844D6F6BaseChangeActual.K) := by
      rw [hz, hφ]
      change Spec.map (CommRingCat.ofHom (RingHom.id
        (S2801E37CoordinateRing S2844D6F6BaseChangeActual.K))) =
        𝟙 (S2801E37AffineScheme S2844D6F6BaseChangeActual.K)
      simp
    have hidZ : S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫
        Over.Hom.left (𝟙 S2844D6F6BaseChangeActual.S2844X) =
        S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ β.left := by
      change S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫
        (𝟙 (S2820E37ProjectiveScheme S2844D6F6BaseChangeActual.K)) =
        S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ β.left
      rw [hZ, hzid]
      simp
    have hid : (𝟙 S2844D6F6BaseChangeActual.S2844X) = β :=
      hglue (𝟙 S2844D6F6BaseChangeActual.S2844X) hidZ (by simpa using hYid.symm)
    exact hid.symm
  · right
    have hzchart : z = S2853ChartZSchemeEndo S2844D6F6BaseChangeActual.K := by
      rw [hz, hφ]
      rfl
    have hZα : S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ alphaOverS2844.left =
        S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ β.left := by
      rw [hZ, hzchart]
      exact hZalpha.symm
    exact (hglue alphaOverS2844 hZα hY.symm).symm


