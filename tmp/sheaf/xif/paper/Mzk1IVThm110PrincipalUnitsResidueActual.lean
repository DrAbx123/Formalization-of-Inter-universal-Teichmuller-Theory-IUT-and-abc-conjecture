import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.FieldTheory.Finite.Basic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110PrincipalUnitsResidueActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NormedField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
/-- Norm bridge with the NNReal-valued NormedField valuation. -/
theorem norm_lt_one_iff_valuation_lt_one (x : K) :
    ‖x‖ < 1 ↔ NormedField.valuation (K := K) x < 1 := by
  constructor
  · intro h
    rw [NormedField.valuation_apply]
    exact (NNReal.coe_lt_coe (r₁ := ‖x‖₊) (r₂ := 1)).mp
      (by simpa [coe_nnnorm] using h)
  · intro h
    rw [NormedField.valuation_apply] at h
    have h' : (‖x‖₊ : ℝ) < 1 :=
      (NNReal.coe_lt_coe (r₁ := ‖x‖₊) (r₂ := 1)).mpr h
    simpa [coe_nnnorm] using h'
abbrev A : ValuationSubring K := (NormedField.valuation (K := K)).valuationSubring

/-- Units of the valuation integer ring are the valuation unit group. -/
noncomputable def integersToA :
    (Integers K) ≃+* (NormedField.valuation (K := K)).valuationSubring where
  toFun (x : Integers K) := ⟨(x : K), by
    change NormedField.valuation (K := K) (x : K) ≤ 1
    exact x.property⟩
  invFun (y : (NormedField.valuation (K := K)).valuationSubring) :=
    ⟨(y : K), by
      change NormedField.valuation (K := K) (y : K) ≤ 1
      exact y.property⟩
  left_inv (x : Integers K) := by ext; rfl
  right_inv (y : (NormedField.valuation (K := K)).valuationSubring) := by ext; rfl
  map_mul' (x y : Integers K) := by ext; rfl
  map_add' (x y : Integers K) := by ext; rfl

noncomputable def integersUnitsEquivUnitGroup :
    (Integers K)ˣ ≃*
      ((NormedField.valuation (K := K)).valuationSubring).unitGroup :=
  (Units.mapEquiv (integersToA (K := K))).trans
    (ValuationSubring.unitGroupMulEquiv (K := K)
      ((NormedField.valuation (K := K)).valuationSubring)).symm

/-- The project principal units are the pullback of the valuation principal unit group. -/
theorem principalUnits_eq_comap_principalUnitGroup :
    principalUnits (K := K) =
      ((ValuationSubring.principalUnitGroup
        ((NormedField.valuation (K := K)).valuationSubring)).comap
        (((NormedField.valuation (K := K)).valuationSubring).unitGroup.subtype)).comap
        (integersUnitsEquivUnitGroup (K := K)).toMonoidHom := by
  ext u
  rw [Subgroup.mem_comap, Subgroup.mem_comap, mem_principalUnits_iff,
    ValuationSubring.mem_principalUnitGroup_iff]
  rw [norm_lt_one_iff_valuation_lt_one]
  have h : ∀ {x : K}, NormedField.valuation (K := K) x < 1 ↔
      ((NormedField.valuation (K := K)).valuationSubring).valuation x < 1 :=
    (Valuation.isEquiv_iff_val_lt_one.mp
      (Valuation.isEquiv_valuation_valuationSubring
        (NormedField.valuation (K := K))))
  have hx := h (x := ((u.val : K) - 1))
  rw [hx]
  congr 1
  simp [integersUnitsEquivUnitGroup, integersToA, Units.mapEquiv]

/-- The quotient by principal units is the residue field unit group. -/
noncomputable def quotientEquivResidueUnits :
    ((NormedField.valuation (K := K)).valuationSubring).unitGroup ⧸
      (ValuationSubring.principalUnitGroup
        ((NormedField.valuation (K := K)).valuationSubring)).comap
        (((NormedField.valuation (K := K)).valuationSubring).unitGroup.subtype) ≃*
      (IsLocalRing.ResidueField
        ((NormedField.valuation (K := K)).valuationSubring))ˣ :=
  ValuationSubring.unitsModPrincipalUnitsEquivResidueFieldUnits
    (A := ((NormedField.valuation (K := K)).valuationSubring))

/-- Card of the quotient equals card of residue units. -/
theorem card_quotient_eq_card_residueUnits
    [Fintype (((NormedField.valuation (K := K)).valuationSubring).unitGroup ⧸
      (ValuationSubring.principalUnitGroup
        ((NormedField.valuation (K := K)).valuationSubring)).comap
        (((NormedField.valuation (K := K)).valuationSubring).unitGroup.subtype))]
    [Fintype (IsLocalRing.ResidueField
      ((NormedField.valuation (K := K)).valuationSubring))ˣ] :
    Fintype.card (((NormedField.valuation (K := K)).valuationSubring).unitGroup ⧸
      (ValuationSubring.principalUnitGroup
        ((NormedField.valuation (K := K)).valuationSubring)).comap
        (((NormedField.valuation (K := K)).valuationSubring).unitGroup.subtype)) =
      Fintype.card (IsLocalRing.ResidueField
        ((NormedField.valuation (K := K)).valuationSubring))ˣ :=
  Fintype.card_congr (quotientEquivResidueUnits (K := K)).toEquiv

/-- Cardinality of a finite residue field is p^f. -/
theorem residue_field_card_exists
    (F : Type*) [Field F] [Fintype F] [CharP F p] :
    ∃ f : ℕ+, Fintype.card F = p ^ (f : ℕ) := by
  obtain ⟨n, hp, hn⟩ := FiniteField.card (K := F) p
  exact ⟨n, hn⟩

/-- Residue units have cardinality p^f-1, coprime to p. -/
theorem residue_units_card_coprime
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F p]
    [Fact (Nat.Prime p)] (f : ℕ+)
    (hcard : Fintype.card F = p ^ (f : ℕ)) :
    Nat.Coprime p (Fintype.card Fˣ) := by
  have hcu : Fintype.card Fˣ = Fintype.card F - 1 :=
    Fintype.card_units (α := F)
  rw [hcu, hcard]
  refine ((Fact.out : Nat.Prime p).coprime_iff_not_dvd).mpr ?_
  intro hdvd
  have hpow : p ∣ p ^ (f : ℕ) := dvd_pow_self p f.pos.ne'
  have h1 : p ∣ 1 := by
    have h0 : p ∣ p ^ (f : ℕ) - (p ^ (f : ℕ) - 1) :=
      Nat.dvd_sub hpow hdvd
    have hsub : p ^ (f : ℕ) - (p ^ (f : ℕ) - 1) = 1 := by
      rw [Nat.sub_sub_self
        (Nat.one_le_pow (f : ℕ) p (Fact.out : Nat.Prime p).pos)]
    simpa [hsub] using h0
  exact (Fact.out : Nat.Prime p).not_dvd_one h1

/-- Quotient transport: project principal quotient is the valuation principal quotient. -/
noncomputable def quotientEquivPrincipalUnits :
    (Integers K)ˣ ⧸ principalUnits (K := K) ≃*
      ((NormedField.valuation (K := K)).valuationSubring).unitGroup ⧸
        (ValuationSubring.principalUnitGroup
          ((NormedField.valuation (K := K)).valuationSubring)).comap
          (((NormedField.valuation (K := K)).valuationSubring).unitGroup.subtype) :=
  QuotientGroup.congr _ _ (integersUnitsEquivUnitGroup (K := K)) (by
    rw [principalUnits_eq_comap_principalUnitGroup]
    exact Subgroup.map_comap_eq_self (f :=
      (integersUnitsEquivUnitGroup (K := K)).toMonoidHom) (by
        have htop : (integersUnitsEquivUnitGroup (K := K)).toMonoidHom.range = ⊤ :=
          MonoidHom.range_eq_top.mpr
            (integersUnitsEquivUnitGroup (K := K)).surjective
        rw [htop]
        exact le_top))

#check quotientEquivPrincipalUnits
#check residue_field_card_exists
#check residue_units_card_coprime
#check card_quotient_eq_card_residueUnits
#check quotientEquivResidueUnits
#check principalUnits_eq_comap_principalUnitGroup
#check integersUnitsEquivUnitGroup
#check norm_lt_one_iff_valuation_lt_one
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110PrincipalUnitsResidueActual
end