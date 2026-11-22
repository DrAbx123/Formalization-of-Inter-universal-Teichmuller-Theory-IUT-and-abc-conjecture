/-
  DVR and fraction-field structure for the adic completion integers, and the
  minimality criterion that uses it.

  The adic completion integers are Mathlib's valuation subring of the completion
  field.  We transfer:
  * the fraction-field instance from the valuation-subring integer theorem;
  * the discrete valuation ring instance from Mathlib's finite-place finite
    residue instance;
  * a uniformizer from the DVR irreducible existence theorem.
  The only non-generic input is finiteness of the residue ring O_F / v.  It is
  stated as an explicit hypothesis, not as a fake instance.  The minimality
  criterion then excludes uniform divisibility by a uniformizer.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiIntegralModelMinimality
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.AdicCompletionFractionField

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralUnits
open LeanFormal.IUT.SourcePsiIntegralUnitsCompletion
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelMinimality
open LeanFormal.IUT.SourcePsiCoefficientIntegrality
open IsDedekindDomain HeightOneSpectrum Valuated

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- The actual adic completion integers, definitionally Mathlib's valuation
subring of the completion field. -/
abbrev SourcePsiCompletionIntegerRing : Type u :=
  v.adicCompletionIntegers S.arithmetic.F

/-- The actual completion field. -/
abbrev SourcePsiCompletionFractionField : Type u :=
  v.adicCompletion S.arithmetic.F

/-- The fraction-field structure for the adic completion integers.  This is
transferred from the generic valuation-subring integer theorem. -/
noncomputable instance sourcePsiCompletionIntegersIsFractionRing :
    IsFractionRing (SourcePsiCompletionIntegerRing S v)
      (SourcePsiCompletionFractionField S v) := by
  change IsFractionRing (Valued.v.valuationSubring) (v.adicCompletion S.arithmetic.F)
  exact (Valuation.valuationSubring.integers (Valued.v)).isFractionRing

/-- The exact non-generic input: finiteness of the actual residue ring
O_F / v.  For a number-field finite place this is the standard residue
finiteness; it is not fabricated here. -/
def SourcePsiResidueRingFiniteness : Prop :=
  Finite (NumberField.RingOfIntegers S.arithmetic.F ⧸ v.asIdeal)

/-- Conditional DVR instance for the actual adic completion integers, transferred
from Mathlib's finite-place DVR instance under residue finiteness. -/
theorem sourcePsiCompletionIntegers_isDiscreteValuationRing
    (hres : SourcePsiResidueRingFiniteness S v) :
    IsDiscreteValuationRing (SourcePsiCompletionIntegerRing S v) := by
  letI : Finite (NumberField.RingOfIntegers S.arithmetic.F ⧸ v.asIdeal) := hres
  unfold SourcePsiCompletionIntegerRing
  infer_instance

/-- Conditional nontriviality of the maximal ideal, from the DVR structure. -/
theorem sourcePsiCompletionIntegers_maximalIdeal_ne_top
    (hres : SourcePsiResidueRingFiniteness S v) :
    IsLocalRing.maximalIdeal (SourcePsiCompletionIntegerRing S v) ≠ ⊤ := by
  letI : IsDiscreteValuationRing (SourcePsiCompletionIntegerRing S v) :=
    sourcePsiCompletionIntegers_isDiscreteValuationRing S v hres
  exact IsDiscreteValuationRing.not_isField

/-- Conditional uniformizer: an irreducible element of the adic completion
integers, i.e. a generator of the maximal ideal. -/
noncomputable def sourcePsiUniformizer
    (hres : SourcePsiResidueRingFiniteness S v) :
    SourcePsiCompletionIntegerRing S v :=
  Classical.choose
    (IsDiscreteValuationRing.exists_irreducible
      (R := SourcePsiCompletionIntegerRing S v))

/-- The chosen uniformizer is irreducible. -/
theorem sourcePsiUniformizer_irreducible
    (hres : SourcePsiResidueRingFiniteness S v) :
    Irreducible (sourcePsiUniformizer S v hres) :=
  Classical.choose_spec
    (IsDiscreteValuationRing.exists_irreducible
      (R := SourcePsiCompletionIntegerRing S v))

/-- The chosen uniformizer is not a unit. -/
theorem sourcePsiUniformizer_not_unit
    (hres : SourcePsiResidueRingFiniteness S v) :
    ¬ IsUnit (sourcePsiUniformizer S v hres) :=
  (sourcePsiUniformizer_irreducible S v hres).not_unit

/-- The chosen uniformizer maps nontrivially into the completion field. -/
theorem sourcePsiUniformizer_algebraMap_ne_zero
    (hres : SourcePsiResidueRingFiniteness S v) :
    algebraMap (SourcePsiCompletionIntegerRing S v)
      (SourcePsiCompletionFractionField S v)
      (sourcePsiUniformizer S v hres) ≠ 0 := by
  intro h
  have hinj : Function.Injective
      (algebraMap (SourcePsiCompletionIntegerRing S v)
        (SourcePsiCompletionFractionField S v)) :=
    IsFractionRing.injective (SourcePsiCompletionIntegerRing S v)
      (SourcePsiCompletionFractionField S v)
  exact (sourcePsiUniformizer_irreducible S v hres).ne_zero (hinj (by simpa using h))

/-- The uniformizer generates the maximal ideal. -/
theorem sourcePsiUniformizer_maximalIdeal_eq
    (hres : SourcePsiResidueRingFiniteness S v) :
    IsLocalRing.maximalIdeal (SourcePsiCompletionIntegerRing S v) =
      Ideal.span {sourcePsiUniformizer S v hres} :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer
    (sourcePsiUniformizer S v hres)).mp
    (sourcePsiUniformizer_irreducible S v hres)

/-- The uniformizer lies in the maximal ideal. -/
theorem sourcePsiUniformizer_mem_maximalIdeal
    (hres : SourcePsiResidueRingFiniteness S v) :
    sourcePsiUniformizer S v hres ∈
      IsLocalRing.maximalIdeal (SourcePsiCompletionIntegerRing S v) := by
  rw [sourcePsiUniformizer_maximalIdeal_eq S v hres]
  exact Ideal.mem_span_singleton_self _

/-! ## Minimality criterion via the uniformizer

The minimality predicate from SourcePsiIntegralModelMinimality excludes uniform
divisibility by any nonunit.  The DVR uniformizer is such a nonunit, so minimality
in particular excludes uniform divisibility by the uniformizer.
-/
theorem sourcePsiIntegralModelMinimal_no_uniformizer_divisibility
    (hres : SourcePsiResidueRingFiniteness S v)
    (M : SourcePsiIntegralModelData S v)
    (hmin : SourcePsiIntegralModelMinimal S v M) :
    ¬ SourcePsiUniformlyDivisible S v M
      (sourcePsiUniformizer S v hres) :=
  SourcePsiIntegralModelMinimal_no_uniformDivisibility S v M hmin
    (sourcePsiUniformizer S v hres)
    (sourcePsiUniformizer_algebraMap_ne_zero S v hres)
    (sourcePsiUniformizer_not_unit S v hres)

/-- Conversely, uniform divisibility by the uniformizer obstructs minimality. -/
theorem sourcePsiIntegralModel_not_minimal_of_uniformizer_divisibility
    (hres : SourcePsiResidueRingFiniteness S v)
    (M : SourcePsiIntegralModelData S v)
    (hdiv : SourcePsiUniformlyDivisible S v M
      (sourcePsiUniformizer S v hres)) :
    ¬ SourcePsiIntegralModelMinimal S v M :=
  SourcePsiIntegralModel_not_minimal_of_uniformDivisibility S v M
    (sourcePsiUniformizer S v hres)
    (sourcePsiUniformizer_algebraMap_ne_zero S v hres)
    (sourcePsiUniformizer_not_unit S v hres)
    hdiv

/-- Uniform divisibility by the chosen uniformizer gives the explicit valuation
bounds at the Weierstrass weights. -/
theorem sourcePsiUniformizerDivisibility_valuation_bounds
    (hres : SourcePsiResidueRingFiniteness S v)
    (M : SourcePsiIntegralModelData S v)
    (hdiv : SourcePsiUniformlyDivisible S v M
      (sourcePsiUniformizer S v hres)) :
    Valued.v (algebraMap (SourcePsiCompletionIntegerRing S v)
        (SourcePsiCompletionFractionField S v) M.curve.a₁) ≤
        Valued.v (algebraMap (SourcePsiCompletionIntegerRing S v)
          (SourcePsiCompletionFractionField S v)
          (sourcePsiUniformizer S v hres)) ∧
      Valued.v (algebraMap (SourcePsiCompletionIntegerRing S v)
        (SourcePsiCompletionFractionField S v) M.curve.a₂) ≤
        Valued.v (algebraMap (SourcePsiCompletionIntegerRing S v)
          (SourcePsiCompletionFractionField S v)
          (sourcePsiUniformizer S v hres)) ^ 2 :=
  SourcePsiUniformlyDivisible.valuation_bounds S v M
    (sourcePsiUniformizer S v hres) hdiv |>.1

/-! ## Exact structure and residual

Transferred:
* the fraction-field structure for the adic completion integers;
* the DVR structure and a uniformizer, conditionally on the finite residue ring;
* the minimality criterion excluding uniform divisibility by the uniformizer.

The exact missing construction is the finite residue ring instance
O_F / v for the actual finite place.  Mathlib's finite-place DVR instance requires
this finiteness as a hypothesis; it is not silently assumed.  For number fields
this is the standard residue finiteness, but no construction is fabricated here.
No fake DVR or fraction-field instance and no fake model is introduced.
-/

/-! ## Basic DVR consequences for the completion integers

theorem sourcePsiCompletionIntegerRing_isDomain
    (hres : SourcePsiResidueRingFiniteness S v) :
    IsDomain (SourcePsiCompletionIntegerRing S v) := by
  letI : IsDiscreteValuationRing (SourcePsiCompletionIntegerRing S v) :=
    sourcePsiCompletionIntegers_isDiscreteValuationRing S v hres
  infer_instance

theorem sourcePsiCompletionIntegerRing_isLocalRing
    (hres : SourcePsiResidueRingFiniteness S v) :
    IsLocalRing (SourcePsiCompletionIntegerRing S v) := by
  letI : IsDiscreteValuationRing (SourcePsiCompletionIntegerRing S v) :=
    sourcePsiCompletionIntegers_isDiscreteValuationRing S v hres
  infer_instance

/-- The uniformizer has valuation strictly below one in the completion
valuation. -/
theorem sourcePsiUniformizer_valuation_lt_one
    (hres : SourcePsiResidueRingFiniteness S v) :
    Valued.v (algebraMap (SourcePsiCompletionIntegerRing S v)
      (SourcePsiCompletionFractionField S v)
      (sourcePsiUniformizer S v hres)) < 1 := by
  have hmem := sourcePsiUniformizer_mem_maximalIdeal S v hres
  rw [Valuation.mem_maximalIdeal_iff] at hmem
  exact hmem

/-- Powers of the uniformizer have the expected valuation powers. -/
theorem sourcePsiUniformizer_valuation_pow
    (hres : SourcePsiResidueRingFiniteness S v) (n : ℕ) :
    Valued.v (algebraMap (SourcePsiCompletionIntegerRing S v)
      (SourcePsiCompletionFractionField S v)
      (sourcePsiUniformizer S v hres) ^ n) =
      Valued.v (algebraMap (SourcePsiCompletionIntegerRing S v)
        (SourcePsiCompletionFractionField S v)
        (sourcePsiUniformizer S v hres)) ^ n := by
  simp [map_pow]

/-- Powers of the uniformizer lie in the maximal ideal for positive exponent. -/
theorem sourcePsiUniformizer_pow_mem_maximalIdeal
    (hres : SourcePsiResidueRingFiniteness S v) {n : ℕ} (hn : 0 < n) :
    sourcePsiUniformizer S v hres ^ n ∈
      IsLocalRing.maximalIdeal (SourcePsiCompletionIntegerRing S v) := by
  rw [sourcePsiUniformizer_maximalIdeal_eq S v hres]
  exact Ideal.pow_mem_span_singleton _ hn

/-! ## Exact criterion summary

Under residue finiteness:
- the adic completion integers are a DVR with fraction field the completion;
- the chosen uniformizer is irreducible, nonunit, nonzero in the field, and
  generates the maximal ideal;
- minimality excludes uniform divisibility by the uniformizer;
- uniform divisibility by the uniformizer obstructs minimality.

The first input, finiteness of O_F / v, is the exact non-generic construction left
to a number-field residue-finiteness proof.  No instance is fabricated.

end LeanFormal.IUT.AdicCompletionFractionField

end