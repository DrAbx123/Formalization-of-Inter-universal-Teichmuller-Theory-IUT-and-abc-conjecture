import tmp.sheaf.xif.paper.Mzk1IVThm110PrincipalUnitsResidueActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithm
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110CardExponentActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110PrincipalUnitsResidueActual
open LeanFormal.IUT.LocalFieldLogarithm
open scoped NormedField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
/-- The explicit uniform exponent: cardinal of the principal-unit quotient. -/
noncomputable def cardExponent : Nat := Nat.card ((Integers K)ˣ ⧸ principalUnits (K := K))
theorem cardExponent_pos [Finite ((Integers K)ˣ ⧸ principalUnits (K := K))] :
    0 < cardExponent (K := K) := by
  letI := Fintype.ofFinite ((Integers K)ˣ ⧸ principalUnits (K := K))
  unfold cardExponent
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_pos
theorem pow_cardExponent_mem
    [Finite ((Integers K)ˣ ⧸ principalUnits (K := K))]
    (u : (Integers K)ˣ) :
    u ^ cardExponent (K := K) ∈ principalUnits (K := K) := by
  letI := Fintype.ofFinite ((Integers K)ˣ ⧸ principalUnits (K := K))
  have hcard : Fintype.card ((Integers K)ˣ ⧸ principalUnits (K := K)) =
      cardExponent (K := K) := by
    unfold cardExponent
    exact (Nat.card_eq_fintype_card).symm
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hcard]
  exact pow_card_eq_one
/-- Card of the quotient equals card of residue units. -/
theorem cardExponent_eq_residueUnits
    [Fintype ((Integers K)ˣ ⧸ principalUnits (K := K))]
    [Fintype (((NormedField.valuation (K := K)).valuationSubring).unitGroup ⧸
      (ValuationSubring.principalUnitGroup
        ((NormedField.valuation (K := K)).valuationSubring)).comap
        (((NormedField.valuation (K := K)).valuationSubring).unitGroup.subtype))]
    [Fintype (IsLocalRing.ResidueField
      ((NormedField.valuation (K := K)).valuationSubring))]
    [DecidableEq (IsLocalRing.ResidueField
      ((NormedField.valuation (K := K)).valuationSubring))] :
    cardExponent (K := K) =
      Fintype.card (IsLocalRing.ResidueField
        ((NormedField.valuation (K := K)).valuationSubring))ˣ := by
  unfold cardExponent
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_congr (quotientEquivPrincipalUnits (K := K)).toEquiv]
  exact card_quotient_eq_card_residueUnits (K := K)

theorem cardExponent_coprime
    [Fintype ((Integers K)ˣ ⧸ principalUnits (K := K))]
    [Fintype (((NormedField.valuation (K := K)).valuationSubring).unitGroup ⧸
      (ValuationSubring.principalUnitGroup
        ((NormedField.valuation (K := K)).valuationSubring)).comap
        (((NormedField.valuation (K := K)).valuationSubring).unitGroup.subtype))]
    [Fintype (IsLocalRing.ResidueField
      ((NormedField.valuation (K := K)).valuationSubring))]
    [DecidableEq (IsLocalRing.ResidueField
      ((NormedField.valuation (K := K)).valuationSubring))]
    [CharP (IsLocalRing.ResidueField
      ((NormedField.valuation (K := K)).valuationSubring)) p]
    [Fact (Nat.Prime p)] (f : ℕ+)
    (hcard : Fintype.card (IsLocalRing.ResidueField
      ((NormedField.valuation (K := K)).valuationSubring)) = p ^ (f : ℕ)) :
    Nat.Coprime p (cardExponent (K := K)) := by
  rw [cardExponent_eq_residueUnits (K := K)]
  exact residue_units_card_coprime
    (IsLocalRing.ResidueField
      ((NormedField.valuation (K := K)).valuationSubring)) f hcard

/-- The redefined core exponent equals the quotient cardinal. -/
theorem integralUnitExponent_eq_cardExponent :
    integralUnitExponent (K := K) = cardExponent (K := K) := rfl

theorem integralUnitExponent_coprime
    [Fintype ((Integers K)ˣ ⧸ principalUnits (K := K))]
    [Fintype (((NormedField.valuation (K := K)).valuationSubring).unitGroup ⧸
      (ValuationSubring.principalUnitGroup
        ((NormedField.valuation (K := K)).valuationSubring)).comap
        (((NormedField.valuation (K := K)).valuationSubring).unitGroup.subtype))]
    [Fintype (IsLocalRing.ResidueField
      ((NormedField.valuation (K := K)).valuationSubring))]
    [DecidableEq (IsLocalRing.ResidueField
      ((NormedField.valuation (K := K)).valuationSubring))]
    [CharP (IsLocalRing.ResidueField
      ((NormedField.valuation (K := K)).valuationSubring)) p]
    [Fact (Nat.Prime p)] (f : ℕ+)
    (hcard : Fintype.card (IsLocalRing.ResidueField
      ((NormedField.valuation (K := K)).valuationSubring)) = p ^ (f : ℕ)) :
    Nat.Coprime p (integralUnitExponent (K := K)) := by
  rw [integralUnitExponent_eq_cardExponent (K := K)]
  exact cardExponent_coprime (K := K) f hcard

#check integralUnitExponent_eq_cardExponent
#check integralUnitExponent_coprime
#check cardExponent_eq_residueUnits
#check cardExponent_coprime
#check cardExponent
#check cardExponent_pos
#check pow_cardExponent_mem
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110CardExponentActual
end