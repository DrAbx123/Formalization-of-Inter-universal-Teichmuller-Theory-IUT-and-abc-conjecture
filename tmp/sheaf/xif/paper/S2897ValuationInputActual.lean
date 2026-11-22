import tmp.sheaf.xif.paper.S2889AffineOrderTwoActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2889AffineOrderTwoActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2897ValuationInputActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

/-- Explicit valuation-at-infinity input on the chart-Z coordinate ring.
The values v(X) = -2, v(Y) = -3 are part of the structure, not proved. -/
structure S2897ValuationInput where
  v : S2801E37CoordinateRing S2844D6F6BaseChangeActual.K →
    WithZero (Multiplicative ℤ)
  vX : v (S2801E37X S2844D6F6BaseChangeActual.K) =
    WithZero.coe (Multiplicative.ofAdd (-2 : ℤ))
  vY : v (S2801E37Y S2844D6F6BaseChangeActual.K) =
    WithZero.coe (Multiplicative.ofAdd (-3 : ℤ))
  v_mul : ∀ a b, v (a * b) = v a * v b
  v_add_le : ∀ a b, v (a + b) ≤ max (v a) (v b)
  v_algebraMap : ∀ c : S2844D6F6BaseChangeActual.K, c ≠ 0 →
    v (algebraMap S2844D6F6BaseChangeActual.K
      (S2801E37CoordinateRing S2844D6F6BaseChangeActual.K) c) = 1

/-- Filtration preservation: φ preserves the valuation. -/
def S2897FiltrationPreserving (V : S2897ValuationInput)
    (φ : S2801E37CoordinateRing S2844D6F6BaseChangeActual.K ≃ₐ[S2844D6F6BaseChangeActual.K]
      S2801E37CoordinateRing S2844D6F6BaseChangeActual.K) : Prop :=
  ∀ z, V.v (φ z) = V.v z

/-- Actual consequence of filtration preservation: φ(X) has the same
valuation as X, namely -2. -/
theorem S2897_value_X (V : S2897ValuationInput)
    (φ : S2801E37CoordinateRing S2844D6F6BaseChangeActual.K ≃ₐ[S2844D6F6BaseChangeActual.K]
      S2801E37CoordinateRing S2844D6F6BaseChangeActual.K)
    (hφ : S2897FiltrationPreserving V φ) :
    V.v (φ (S2801E37X S2844D6F6BaseChangeActual.K)) =
      V.v (S2801E37X S2844D6F6BaseChangeActual.K) :=
  hφ _

/-- Exact missing X-fixed lemma: order-two and filtration preservation force
φ(X)=X. -/
def S2897XFixedInput (V : S2897ValuationInput) : Prop :=
  ∀ φ : S2801E37CoordinateRing S2844D6F6BaseChangeActual.K ≃ₐ[S2844D6F6BaseChangeActual.K]
      S2801E37CoordinateRing S2844D6F6BaseChangeActual.K,
    φ.toRingHom.comp φ.toRingHom =
        RingHom.id (S2801E37CoordinateRing S2844D6F6BaseChangeActual.K) →
    S2897FiltrationPreserving V φ →
      φ (S2801E37X S2844D6F6BaseChangeActual.K) =
        S2801E37X S2844D6F6BaseChangeActual.K

/-- Conditional X-fixed statement: if the valuation provides the missing
X-fixed input, then φ(X)=X follows. -/
theorem S2896XFixed_of_valuation
    (V : S2897ValuationInput)
    (hX : S2897XFixedInput V)
    (φ : S2801E37CoordinateRing S2844D6F6BaseChangeActual.K ≃ₐ[S2844D6F6BaseChangeActual.K]
      S2801E37CoordinateRing S2844D6F6BaseChangeActual.K)
    (hφ2 : φ.toRingHom.comp φ.toRingHom =
      RingHom.id (S2801E37CoordinateRing S2844D6F6BaseChangeActual.K))
    (hfil : S2897FiltrationPreserving V φ) :
    φ (S2801E37X S2844D6F6BaseChangeActual.K) =
      S2801E37X S2844D6F6BaseChangeActual.K :=
  hX φ hφ2 hfil

/-!
## First missing object

The X-fixed lemma S2897XFixedInput is not proved.  A proof needs:

1. a valuation/degree theory on the quotient S2801E37CoordinateRing that
   descends from the polynomial degree (S2896_naive_totalDegree_not_wellDefined
   shows naive total degree does not descend);
2. the classification of order-two K-algebra automorphisms of the coordinate
   ring, or a direct coefficient/filtration argument showing that an order-two
   filtration-preserving automorphism sends X to an element of valuation -2
   that must be X (and similarly for Y);
3. the exclusion of translation-like automorphisms via the origin-preserving
   condition.

No valuation or X-fixed lemma is fabricated; the structure only records the
explicit input.
-/

#check S2897ValuationInput
#check S2897FiltrationPreserving
#check S2897_value_X
#check S2897XFixedInput
#check S2896XFixed_of_valuation
#print axioms S2896XFixed_of_valuation

end LeanFormal.IUT.XiFPaper.S2897ValuationInputActual
end
