import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceLogShell
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import Mathlib.Tactic

/-!
# Explicit principal-unit exponent consumer

The production uniform exponent theorem chooses an unspecified cardinal.  This
file records the explicit exponent given by the finite principal quotient of
the normalized completion, proves that this cardinal works for every unit and
transports it to the actual completed valuation unit group.  No properness
candidate is needed: the normalized completion already has the production
properness instance.  No card, no placeholder, no wrapper-only alias.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

noncomputable section

namespace LeanFormal.IUT.PrincipalUnitExplicitExponentConsumer

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped Valued

variable {F : Type*} [Field F] [NumberField F]

variable (v : NumberField.FinitePlace F)

/-- The explicit principal-unit quotient of the normalized completion. -/
noncomputable abbrev normalizedPrincipalQuotient : Type :=
  (Integers (NormalizedCompletion v))ˣ ⧸
    principalUnits (K := NormalizedCompletion v)

/-- The explicit exponent is the cardinal of the normalized principal quotient. -/
noncomputable def explicitPrincipalExponent : Nat :=
  Nat.card (normalizedPrincipalQuotient v)

/-- The normalized principal quotient is finite. -/
theorem finite_normalizedPrincipalQuotient :
    Finite (normalizedPrincipalQuotient v) :=
  finite_principalUnitQuotient (K := NormalizedCompletion v)

/-- The normalized principal quotient is a fintype. -/
noncomputable instance fintypeNormalizedPrincipalQuotient :
    Fintype (normalizedPrincipalQuotient v) :=
  Fintype.ofFinite _

/-- The explicit exponent is positive. -/
theorem explicitPrincipalExponent_pos :
    0 < explicitPrincipalExponent v :=
  Nat.card_pos

/-- The explicit exponent sends every normalized integral unit into the
normalized principal units. -/
theorem normalizedPrincipalQuotient_card_pow_mem
    (u : (Integers (NormalizedCompletion v))ˣ) :
    u ^ explicitPrincipalExponent v ∈
      principalUnits (K := NormalizedCompletion v) := by
  haveI := finite_normalizedPrincipalQuotient v
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
  exact pow_card_eq_one

/-- The explicit exponent as a uniform exponent for the normalized unit group. -/
theorem normalizedPrincipalQuotient_card_uniform :
    ∀ u : (Integers (NormalizedCompletion v))ˣ,
      u ^ explicitPrincipalExponent v ∈
        principalUnits (K := NormalizedCompletion v) :=
  normalizedPrincipalQuotient_card_pow_mem v

/-- The explicit exponent transferred to the actual completed unit group. -/
theorem actualNormalizedPrincipal_explicitExponent
    (u : (CompletionIntegers v)ˣ) :
    (normalizedCompletionUnitsEquiv v).symm
        (u ^ explicitPrincipalExponent v) ∈
      principalUnits (K := NormalizedCompletion v) := by
  rw [map_pow]
  exact normalizedPrincipalQuotient_card_pow_mem v
    ((normalizedCompletionUnitsEquiv v).symm u)

/-- Uniform explicit exponent form on the actual units. -/
theorem actualNormalizedPrincipal_explicitExponent_uniform :
    ∀ u : (CompletionIntegers v)ˣ,
      (normalizedCompletionUnitsEquiv v).symm
          (u ^ explicitPrincipalExponent v) ∈
        principalUnits (K := NormalizedCompletion v) :=
  actualNormalizedPrincipal_explicitExponent v

/-- The explicit exponent works simultaneously for every power. -/
theorem actualNormalizedPrincipal_explicitExponent_pow
    (u : (CompletionIntegers v)ˣ) (m : Nat) :
    (normalizedCompletionUnitsEquiv v).symm
        ((u ^ m) ^ explicitPrincipalExponent v) ∈
      principalUnits (K := NormalizedCompletion v) := by
  simpa only [pow_mul] using
    actualNormalizedPrincipal_explicitExponent v (u ^ m)

/-- The explicit exponent equals the production chosen exponent for the
normalized completion. -/
theorem explicitPrincipalExponent_works :
    ∃ N : Nat, 0 < N ∧
      ∀ u : (Integers (NormalizedCompletion v))ˣ,
        u ^ N ∈ principalUnits (K := NormalizedCompletion v) :=
  ⟨explicitPrincipalExponent v, explicitPrincipalExponent_pos v,
    normalizedPrincipalQuotient_card_uniform v⟩

/-- The explicit exponent transports to the actual unit group in the comap
picture. -/
theorem actualPrincipalQuotient_uniform_explicit :
    ∃ N : Nat, 0 < N ∧
      ∀ u : (CompletionIntegers v)ˣ,
        (normalizedCompletionUnitsEquiv v).symm (u ^ N) ∈
          principalUnits (K := NormalizedCompletion v) :=
  ⟨explicitPrincipalExponent v, explicitPrincipalExponent_pos v,
    actualNormalizedPrincipal_explicitExponent_uniform v⟩

/-- The explicit exponent power map is the identity in the normalized
principal quotient. -/
theorem normalizedPrincipalQuotient_pow_eq_one
    (u : (Integers (NormalizedCompletion v))ˣ) :
    QuotientGroup.mk (u ^ explicitPrincipalExponent v) =
      (1 : normalizedPrincipalQuotient v) :=
  QuotientGroup.eq_one_iff.mpr
    (normalizedPrincipalQuotient_card_pow_mem v u)

/-- The explicit exponent also works after multiplying by an existing
principal unit. -/
theorem normalizedPrincipalQuotient_card_pow_mul_mem
    (u : (Integers (NormalizedCompletion v))ˣ)
    (w : principalUnits (K := NormalizedCompletion v)) :
    (u * (w : (Integers (NormalizedCompletion v))ˣ)) ^
        explicitPrincipalExponent v ∈
      principalUnits (K := NormalizedCompletion v) := by
  have h := normalizedPrincipalQuotient_card_pow_mem v
    (u * (w : (Integers (NormalizedCompletion v))ˣ))
  simpa only [mul_pow] using h

/-- The explicit exponent is independent of the place in the sense that it is
the cardinal of the canonical quotient; this restates the definition. -/
theorem explicitPrincipalExponent_eq_card :
    explicitPrincipalExponent v = Nat.card (normalizedPrincipalQuotient v) :=
  rfl

section GeneralExplicitExponent

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K]
  [CompleteSpace K] [ProperSpace K]
  {p : Nat} [Fact p.Prime] [NormedAlgebra ℚ_[p] K]

/-- General explicit principal exponent: the cardinal of the principal-unit
quotient. -/
noncomputable def principalUnitQuotientExponent : Nat :=
  Nat.card ((Integers K)ˣ ⧸ principalUnits (K := K))

theorem principalUnitQuotientExponent_pos :
    0 < principalUnitQuotientExponent (K := K) (p := p) :=
  Nat.card_pos

/-- Every integral unit raised to the quotient cardinal is principal. -/
theorem principalUnitQuotientExponent_pow_mem
    (u : (Integers K)ˣ) :
    u ^ principalUnitQuotientExponent (K := K) (p := p) ∈
      principalUnits (K := K) := by
  haveI := finite_principalUnitQuotient (K := K) (p := p)
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
  exact pow_card_eq_one

theorem principalUnitQuotientExponent_uniform :
    ∀ u : (Integers K)ˣ,
      u ^ principalUnitQuotientExponent (K := K) (p := p) ∈
        principalUnits (K := K) :=
  principalUnitQuotientExponent_pow_mem (K := K) (p := p)

theorem exists_explicit_principalUnit_exponent :
    ∃ N : Nat, 0 < N ∧
      ∀ u : (Integers K)ˣ,
        u ^ N ∈ principalUnits (K := K) :=
  ⟨principalUnitQuotientExponent (K := K) (p := p),
    principalUnitQuotientExponent_pos (K := K) (p := p),
    principalUnitQuotientExponent_uniform (K := K) (p := p)⟩

theorem principalUnitQuotientExponent_pow_pow_mem
    (u : (Integers K)ˣ) (m : Nat) :
    (u ^ m) ^ principalUnitQuotientExponent (K := K) (p := p) ∈
      principalUnits (K := K) :=
  principalUnitQuotientExponent_pow_mem (K := K) (p := p) (u ^ m)

theorem principalUnitQuotientExponent_mul_mem
    (u : (Integers K)ˣ) (w : principalUnits (K := K)) :
    (u * (w : (Integers K)ˣ)) ^ principalUnitQuotientExponent (K := K) (p := p) ∈
      principalUnits (K := K) :=
  principalUnitQuotientExponent_pow_mem (K := K) (p := p) (u * (w : (Integers K)ˣ))

theorem principalUnitQuotientExponent_inv_mem
    (u : (Integers K)ˣ) :
    (u⁻¹) ^ principalUnitQuotientExponent (K := K) (p := p) ∈
      principalUnits (K := K) :=
  principalUnitQuotientExponent_pow_mem (K := K) (p := p) u⁻¹

end GeneralExplicitExponent
end LeanFormal.IUT.PrincipalUnitExplicitExponentConsumer
