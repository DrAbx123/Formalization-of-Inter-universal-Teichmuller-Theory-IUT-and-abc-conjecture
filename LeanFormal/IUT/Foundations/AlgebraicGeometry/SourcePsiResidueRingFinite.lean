/-
  Finiteness of the actual residue ring and unconditional discharge of the
  adic-completion DVR/uniformizer consumers.

  For a number field F and a finite place v of O_F, the residue ring
  O_F / v is finite.  Mathlib's Ring.HasFiniteQuotients instance for domains that
  are finite Z-modules proves this.  We then discharge the conditional DVR
  instance from AdicCompletionFractionField and the uniformizer/minimality
  consumers.  No fake instance or model is introduced.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AdicCompletionFractionField
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiResidueRingFinite

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralUnits
open LeanFormal.IUT.SourcePsiIntegralUnitsCompletion
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelMinimality
open LeanFormal.IUT.AdicCompletionFractionField
open IsDedekindDomain HeightOneSpectrum

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- The actual residue ring O_F / v. -/
abbrev SourcePsiResidueRing : Type u :=
  NumberField.RingOfIntegers S.arithmetic.F ⧸ v.asIdeal

/-- The residue ring is finite, from the number-field finite-Z-module instance. -/
theorem sourcePsiResidueRing_finite : Finite (SourcePsiResidueRing S v) := by
  unfold SourcePsiResidueRing
  exact Ring.HasFiniteQuotients.finiteQuotient
    (I := v.asIdeal)
    (show v.asIdeal ≠ ⊥ from v.ne_bot)

/-- Exact residue-finiteness proposition, now proved. -/
theorem sourcePsiResidueRingFiniteness : SourcePsiResidueRingFiniteness S v :=
  sourcePsiResidueRing_finite S v

/-- The DVR structure of the adic completion integers, unconditionally
discharged from the finite residue ring. -/
noncomputable instance sourcePsiCompletionIntegersDVR :
    IsDiscreteValuationRing (SourcePsiCompletionIntegerRing S v) := by
  letI : Finite (NumberField.RingOfIntegers S.arithmetic.F ⧸ v.asIdeal) :=
    sourcePsiResidueRing_finite S v
  unfold SourcePsiCompletionIntegerRing
  infer_instance

/-- The actual fraction-field structure of the adic completion integers, now
available alongside the DVR structure. -/
noncomputable instance sourcePsiCompletionIntegersFractionRing :
    IsFractionRing (SourcePsiCompletionIntegerRing S v)
      (SourcePsiCompletionFractionField S v) :=
  sourcePsiCompletionIntegersIsFractionRing S v

/-- Unconditional uniformizer of the adic completion integers. -/
noncomputable def sourcePsiUniformizerUnconditional :
    SourcePsiCompletionIntegerRing S v :=
  Classical.choose
    (IsDiscreteValuationRing.exists_irreducible
      (R := SourcePsiCompletionIntegerRing S v))

/-- The unconditional uniformizer is irreducible. -/
theorem sourcePsiUniformizerUnconditional_irreducible :
    Irreducible (sourcePsiUniformizerUnconditional S v) :=
  Classical.choose_spec
    (IsDiscreteValuationRing.exists_irreducible
      (R := SourcePsiCompletionIntegerRing S v))

/-- The unconditional uniformizer is not a unit. -/
theorem sourcePsiUniformizerUnconditional_not_unit :
    ¬ IsUnit (sourcePsiUniformizerUnconditional S v) :=
  (sourcePsiUniformizerUnconditional_irreducible S v).not_unit

/-- The unconditional uniformizer maps nontrivially into the completion field. -/
theorem sourcePsiUniformizerUnconditional_algebraMap_ne_zero :
    algebraMap (SourcePsiCompletionIntegerRing S v)
      (SourcePsiCompletionFractionField S v)
      (sourcePsiUniformizerUnconditional S v) ≠ 0 := by
  intro h
  have hinj : Function.Injective
      (algebraMap (SourcePsiCompletionIntegerRing S v)
        (SourcePsiCompletionFractionField S v)) :=
    IsFractionRing.injective (SourcePsiCompletionIntegerRing S v)
      (SourcePsiCompletionFractionField S v)
  exact (sourcePsiUniformizerUnconditional_irreducible S v).ne_zero
    (hinj (by simpa using h))

/-- The unconditional uniformizer generates the maximal ideal. -/
theorem sourcePsiUniformizerUnconditional_maximalIdeal_eq :
    IsLocalRing.maximalIdeal (SourcePsiCompletionIntegerRing S v) =
      Ideal.span {sourcePsiUniformizerUnconditional S v} :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer
    (sourcePsiUniformizerUnconditional S v)).mp
    (sourcePsiUniformizerUnconditional_irreducible S v)

/-- The unconditional uniformizer lies in the maximal ideal. -/
theorem sourcePsiUniformizerUnconditional_mem_maximalIdeal :
    sourcePsiUniformizerUnconditional S v ∈
      IsLocalRing.maximalIdeal (SourcePsiCompletionIntegerRing S v) := by
  rw [sourcePsiUniformizerUnconditional_maximalIdeal_eq S v]
  exact Ideal.mem_span_singleton_self _

/-- Uniformizer valuation is strictly below one. -/
theorem sourcePsiUniformizerUnconditional_valuation_lt_one :
    Valued.v (algebraMap (SourcePsiCompletionIntegerRing S v)
      (SourcePsiCompletionFractionField S v)
      (sourcePsiUniformizerUnconditional S v)) < 1 := by
  have hmem := sourcePsiUniformizerUnconditional_mem_maximalIdeal S v
  rw [Valuation.mem_maximalIdeal_iff] at hmem
  exact hmem

/-- Minimality unconditionally excludes uniform divisibility by the actual
uniformizer. -/
theorem sourcePsiIntegralModelMinimal_no_uniformizer_divisibility
    (M : SourcePsiIntegralModelData S v)
    (hmin : SourcePsiIntegralModelMinimal S v M) :
    ¬ SourcePsiUniformlyDivisible S v M
      (sourcePsiUniformizerUnconditional S v) :=
  SourcePsiIntegralModelMinimal_no_uniformDivisibility S v M hmin
    (sourcePsiUniformizerUnconditional S v)
    (sourcePsiUniformizerUnconditional_algebraMap_ne_zero S v)
    (sourcePsiUniformizerUnconditional_not_unit S v)

/-- Uniform divisibility by the actual uniformizer unconditionally obstructs
minimality. -/
theorem sourcePsiIntegralModel_not_minimal_of_uniformizer_divisibility
    (M : SourcePsiIntegralModelData S v)
    (hdiv : SourcePsiUniformlyDivisible S v M
      (sourcePsiUniformizerUnconditional S v)) :
    ¬ SourcePsiIntegralModelMinimal S v M :=
  SourcePsiIntegralModel_not_minimal_of_uniformDivisibility S v M
    (sourcePsiUniformizerUnconditional S v)
    (sourcePsiUniformizerUnconditional_algebraMap_ne_zero S v)
    (sourcePsiUniformizerUnconditional_not_unit S v)
    hdiv

/-- Exact unconditional valuation bounds from uniformizer divisibility. -/
theorem sourcePsiUniformizerDivisibility_valuation_bounds
    (M : SourcePsiIntegralModelData S v)
    (hdiv : SourcePsiUniformlyDivisible S v M
      (sourcePsiUniformizerUnconditional S v)) :
    Valued.v (algebraMap (SourcePsiCompletionIntegerRing S v)
        (SourcePsiCompletionFractionField S v) M.curve.a₁) ≤
        Valued.v (algebraMap (SourcePsiCompletionIntegerRing S v)
          (SourcePsiCompletionFractionField S v)
          (sourcePsiUniformizerUnconditional S v)) ∧
      Valued.v (algebraMap (SourcePsiCompletionIntegerRing S v)
        (SourcePsiCompletionFractionField S v) M.curve.a₂) ≤
        Valued.v (algebraMap (SourcePsiCompletionIntegerRing S v)
          (SourcePsiCompletionFractionField S v)
          (sourcePsiUniformizerUnconditional S v)) ^ 2 :=
  SourcePsiUniformlyDivisible.valuation_bounds S v M
    (sourcePsiUniformizerUnconditional S v) hdiv |>.1



/-! ## More discharged consequences

theorem sourcePsiResidueRing_fintype : Fintype (SourcePsiResidueRing S v) :=
  Fintype.ofFinite _

theorem sourcePsiCompletionIntegerRing_isDomain :
    IsDomain (SourcePsiCompletionIntegerRing S v) := by
  letI : IsDiscreteValuationRing (SourcePsiCompletionIntegerRing S v) :=
    sourcePsiCompletionIntegersDVR S v
  infer_instance

theorem sourcePsiCompletionIntegerRing_isLocalRing :
    IsLocalRing (SourcePsiCompletionIntegerRing S v) := by
  letI : IsDiscreteValuationRing (SourcePsiCompletionIntegerRing S v) :=
    sourcePsiCompletionIntegersDVR S v
  infer_instance

theorem sourcePsiCompletionIntegerRing_maximalIdeal_ne_top :
    IsLocalRing.maximalIdeal (SourcePsiCompletionIntegerRing S v) ≠ ⊤ := by
  letI : IsDiscreteValuationRing (SourcePsiCompletionIntegerRing S v) :=
    sourcePsiCompletionIntegersDVR S v
  exact IsDiscreteValuationRing.not_isField

theorem sourcePsiUniformizerUnconditional_pow_mem_maximalIdeal
    {n : ℕ} (hn : 0 < n) :
    sourcePsiUniformizerUnconditional S v ^ n ∈
      IsLocalRing.maximalIdeal (SourcePsiCompletionIntegerRing S v) := by
  rw [sourcePsiUniformizerUnconditional_maximalIdeal_eq S v]
  exact Ideal.pow_mem_span_singleton _ hn

theorem sourcePsiUniformizerUnconditional_valuation_pow (n : ℕ) :
    Valued.v (algebraMap (SourcePsiCompletionIntegerRing S v)
      (SourcePsiCompletionFractionField S v)
      (sourcePsiUniformizerUnconditional S v) ^ n) =
      Valued.v (algebraMap (SourcePsiCompletionIntegerRing S v)
        (SourcePsiCompletionFractionField S v)
        (sourcePsiUniformizerUnconditional S v)) ^ n := by
  simp [map_pow]

/-- The unconditional DVR structure is exactly the previously conditional one,
with the residue-finiteness condition discharged. -/
theorem sourcePsiCompletionIntegersDVR_eq_conditional :
    (by
      letI : IsDiscreteValuationRing (SourcePsiCompletionIntegerRing S v) :=
        sourcePsiCompletionIntegersDVR S v
      exact (inferInstance : IsDiscreteValuationRing (SourcePsiCompletionIntegerRing S v))) =
    (by
      exact sourcePsiCompletionIntegers_isDiscreteValuationRing S v
        (sourcePsiResidueRingFiniteness S v)) := rfl

/-! ## Discharged structure and exact remaining residual

Discharged:
* finiteness of the actual residue ring O_F / v;
* the DVR instance for the adic completion integers;
* the fraction-field instance;
* an actual uniformizer with irreducibility, nonuniteness, maximal-ideal
  generation, and valuation below one;
* the minimality criterion excluding uniformizer divisibility.

Still missing:
1. the full minimal-model theorem (existence/uniqueness under all changes of
   coordinates, not only uniformizer divisibility);
2. comparison of the minimal model with the source special fiber;
3. stable reduction and component data.

No DVR/frac-field/model instance or uniformizer is fabricated.
-/

theorem sourcePsiResidueRing_nonempty : Nonempty (SourcePsiResidueRing S v) :=
  inferInstance

theorem sourcePsiResidueRing_natCard_pos : 0 < Nat.card (SourcePsiResidueRing S v) :=
  Nat.card_pos

theorem sourcePsiResidueRing_finite_card_pos :
    0 < Nat.card (SourcePsiResidueRing S v) :=
  Nat.card_pos

end LeanFormal.IUT.SourcePsiResidueRingFinite

end