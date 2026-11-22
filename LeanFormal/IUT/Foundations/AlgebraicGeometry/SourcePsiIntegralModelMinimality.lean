/-
  Minimality criterion and obstruction for the actual integral Weierstrass model.

  Let R be the adic completion integers and K their fraction field.  An integral
  model is minimal when every Weierstrass change of coordinates over K with
  integral transformed coefficients has unit scaling factor.  A nonunit pi with
  uniform divisibility of the coefficients at the Weierstrass weights produces an
  explicit integral scaling and obstructs minimality.  Coefficient integrality
  alone only constructs a raw model; minimality is an additional condition and is
  the exact residual.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiCoefficientIntegrality

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiIntegralModelMinimality

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralUnits
open LeanFormal.IUT.SourcePsiIntegralUnitsCompletion
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiCoefficientIntegrality
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- Integrality of all five coefficients of a Weierstrass curve over K, i.e.
membership in the image of the adic completion integers. -/
def SourcePsiIntegralWeierstrassCurve
    (W : WeierstrassCurve (SourcePsiCompletionField S v)) : Prop :=
  (∃ a₁ : SourcePsiCompletionIntegers S v,
    algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) a₁ = W.a₁) ∧
  (∃ a₂ : SourcePsiCompletionIntegers S v,
    algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) a₂ = W.a₂) ∧
  (∃ a₃ : SourcePsiCompletionIntegers S v,
    algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) a₃ = W.a₃) ∧
  (∃ a₄ : SourcePsiCompletionIntegers S v,
    algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) a₄ = W.a₄) ∧
  (∃ a₆ : SourcePsiCompletionIntegers S v,
    algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) a₆ = W.a₆)

/-- A field element is a completion integral unit when it is the image of a unit
of the adic completion integers. -/
def IsCompletionIntegralUnit
    (x : SourcePsiCompletionField S v) : Prop :=
  ∃ r : (SourcePsiCompletionIntegers S v)ˣ,
    algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v)
        (r : SourcePsiCompletionIntegers S v) = x

/-- The actual base-changed source curve over K. -/
abbrev SourcePsiMinimalityBaseCurve : WeierstrassCurve (SourcePsiCompletionField S v) :=
  SourcePsiBaseChangedCurve S v

/-- Minimality of an integral model: every change of coordinates over K with
integral transformed coefficients has an integral unit scaling factor. -/
def SourcePsiIntegralModelMinimal
    (M : SourcePsiIntegralModelData S v) : Prop :=
  ∀ C : VariableChange (SourcePsiCompletionField S v),
    SourcePsiIntegralWeierstrassCurve S v
        (C • (M.curve.map
          (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v)))) →
      IsCompletionIntegralUnit S v (C.u : SourcePsiCompletionField S v)

/-- Uniform divisibility at the Weierstrass weights: a nonunit pi divides
a1 by pi, a2 by pi^2, a3 by pi^3, a4 by pi^4, a6 by pi^6. -/
def SourcePsiUniformlyDivisible
    (M : SourcePsiIntegralModelData S v) (π : SourcePsiCompletionIntegers S v) : Prop :=
  ∃ b₁ b₂ b₃ b₄ b₆ : SourcePsiCompletionIntegers S v,
    M.curve.a₁ = π * b₁ ∧
    M.curve.a₂ = π ^ 2 * b₂ ∧
    M.curve.a₃ = π ^ 3 * b₃ ∧
    M.curve.a₄ = π ^ 4 * b₄ ∧
    M.curve.a₆ = π ^ 6 * b₆

/-- The explicit uniform scaling change with u = pi and r = s = t = 0. -/
noncomputable def sourcePsiUniformScaling
    (π : SourcePsiCompletionIntegers S v)
    (hπ : algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) π ≠ 0) :
    VariableChange (SourcePsiCompletionField S v) where
  u := Units.mk0
    (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) π) hπ
  r := 0
  s := 0
  t := 0

/-- A nonunit pi with uniform divisibility makes the explicit scaling change
integral in all five coefficients. -/
theorem sourcePsiUniformScaling_integral
    (M : SourcePsiIntegralModelData S v)
    (π : SourcePsiCompletionIntegers S v)
    (hπ0 : algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) π ≠ 0)
    (hdiv : SourcePsiUniformlyDivisible S v M π) :
    SourcePsiIntegralWeierstrassCurve S v
      (sourcePsiUniformScaling S v π hπ0 •
        (M.curve.map
          (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v)))) := by
  obtain ⟨b₁, b₂, b₃, b₄, b₆, h₁, h₂, h₃, h₄, h₆⟩ := hdiv
  refine ⟨⟨b₁, ?_⟩, ⟨b₂, ?_⟩, ⟨b₃, ?_⟩, ⟨b₄, ?_⟩, ⟨b₆, ?_⟩⟩
  · simp [sourcePsiUniformScaling, WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.map, h₁]
  · simp [sourcePsiUniformScaling, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.map, h₂]
  · simp [sourcePsiUniformScaling, WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.map, h₃]
  · simp [sourcePsiUniformScaling, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.map, h₄]
  · simp [sourcePsiUniformScaling, WeierstrassCurve.variableChange_a₆,
      WeierstrassCurve.map, h₆]

/-- The scaling factor of the explicit uniform scaling is not an integral unit
when pi is not a unit of the adic completion integers. -/
theorem sourcePsiUniformScaling_not_unit
    (π : SourcePsiCompletionIntegers S v)
    (hπ0 : algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) π ≠ 0)
    (hπ : ¬ IsUnit π) :
    ¬ IsCompletionIntegralUnit S v
      (sourcePsiUniformScaling S v π hπ0).u := by
  rintro ⟨r, hr⟩
  apply hπ
  apply IsUnit.of_map
    (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v))
  · exact IsLocalRing.algebraMap_isUnit_of_isUnit
  · rwa [hr]

/-- A nonunit uniform divisibility obstructs minimality of the actual integral
model. -/
theorem SourcePsiIntegralModel_not_minimal_of_uniformDivisibility
    (M : SourcePsiIntegralModelData S v)
    (π : SourcePsiCompletionIntegers S v)
    (hπ0 : algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) π ≠ 0)
    (hπ : ¬ IsUnit π)
    (hdiv : SourcePsiUniformlyDivisible S v M π) :
    ¬ SourcePsiIntegralModelMinimal S v M := by
  intro hmin
  exact (sourcePsiUniformScaling_not_unit S v π hπ0 hπ)
    (hmin (sourcePsiUniformScaling S v π hπ0)
      (sourcePsiUniformScaling_integral S v M π hπ0 hdiv))

/-- Minimality implies no nonunit uniform divisibility of an actual model. -/
theorem SourcePsiIntegralModelMinimal_no_uniformDivisibility
    (M : SourcePsiIntegralModelData S v)
    (hmin : SourcePsiIntegralModelMinimal S v M)
    (π : SourcePsiCompletionIntegers S v)
    (hπ0 : algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) π ≠ 0)
    (hπ : ¬ IsUnit π) :
    ¬ SourcePsiUniformlyDivisible S v M π :=
  fun hdiv =>
    SourcePsiIntegralModel_not_minimal_of_uniformDivisibility S v M π hπ0 hπ hdiv hmin

/-- Minimal model residual: an actual integral model together with minimality.
No inhabitant is asserted. -/
def SourcePsiIntegralModelMinimalityResidual : Prop :=
  ∃ M : SourcePsiIntegralModelData S v, SourcePsiIntegralModelMinimal S v M



/-! ## Valuation form of uniform divisibility

/-- Uniform divisibility gives the expected valuation bounds at the Weierstrass
weights. -/
theorem SourcePsiUniformlyDivisible.valuation_bounds
    (M : SourcePsiIntegralModelData S v)
    (π : SourcePsiCompletionIntegers S v)
    (hdiv : SourcePsiUniformlyDivisible S v M π) :
    Valued.v (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) M.curve.a₁) ≤
        Valued.v (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) π) ∧
      Valued.v (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) M.curve.a₂) ≤
        Valued.v (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) π) ^ 2 ∧
      Valued.v (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) M.curve.a₃) ≤
        Valued.v (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) π) ^ 3 ∧
      Valued.v (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) M.curve.a₄) ≤
        Valued.v (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) π) ^ 4 ∧
      Valued.v (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) M.curve.a₆) ≤
        Valued.v (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) π) ^ 6 := by
  obtain ⟨b₁, b₂, b₃, b₄, b₆, h₁, h₂, h₃, h₄, h₆⟩ := hdiv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h₁]; simp [map_mul]
  · rw [h₂]; simp [map_mul, map_pow]
  · rw [h₃]; simp [map_mul, map_pow]
  · rw [h₄]; simp [map_mul, map_pow]
  · rw [h₆]; simp [map_mul, map_pow]

/-- Exact residual form: a nonunit uniform divisibility is a non-minimality
obstruction; no converse is asserted here beyond the explicit scaling class. -/
theorem SourcePsiIntegralModelMinimality_obstruction
    (M : SourcePsiIntegralModelData S v)
    (π : SourcePsiCompletionIntegers S v)
    (hπ0 : algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) π ≠ 0)
    (hπ : ¬ IsUnit π)
    (hdiv : SourcePsiUniformlyDivisible S v M π) :
    ¬ SourcePsiIntegralModelMinimal S v M :=
  SourcePsiIntegralModel_not_minimal_of_uniformDivisibility S v M π hπ0 hπ hdiv

/-- The minimal model residual is exactly an actual integral model with the
minimality condition; no inhabitant is constructed. -/
theorem SourcePsiIntegralModelMinimalityResidual_iff :
    SourcePsiIntegralModelMinimalityResidual S v ↔
      ∃ M : SourcePsiIntegralModelData S v, SourcePsiIntegralModelMinimal S v M :=
  Iff.rfl

/-! ## Exact minimality residual

The raw coefficient-integrality model exists when the five coefficients are
integral.  Minimality is a separate condition: no Weierstrass change over K with
integral transformed coefficients and nonunit scaling factor.  A sufficient
obstruction is a nonunit pi with uniform divisibility of the coefficients at
weights 1,2,3,4,6; the explicit scaling change then gives integral coefficients
and a nonunit scaling factor.

Still missing:
1. a proof that the adic completion integers form a discrete valuation ring with
   the actual K as fraction field, in the exact Mathlib typeclass form;
2. the full minimal-model theorem (existence and uniqueness under all changes of
   coordinates, not only uniform scalings);
3. comparison of the minimal model with the source special fiber;
4. stable reduction and component data.

These are exact residual objects, not cards.  No model is fabricated.


/-! ## Unit and minimality API

theorem IsCompletionIntegralUnit.one :
    IsCompletionIntegralUnit S v
      (1 : SourcePsiCompletionField S v) :=
  ⟨1, by simp⟩

theorem IsCompletionIntegralUnit.mul
    {x y : SourcePsiCompletionField S v}
    (hx : IsCompletionIntegralUnit S v x)
    (hy : IsCompletionIntegralUnit S v y) :
    IsCompletionIntegralUnit S v (x * y) := by
  obtain ⟨r, rfl⟩ := hx
  obtain ⟨s, rfl⟩ := hy
  exact ⟨r * s, by simp⟩

theorem IsCompletionIntegralUnit.inv
    {x : SourcePsiCompletionField S v}
    (hx : IsCompletionIntegralUnit S v x) :
    IsCompletionIntegralUnit S v x⁻¹ := by
  obtain ⟨r, rfl⟩ := hx
  exact ⟨r⁻¹, by simp⟩

/-- Unfolding form of the minimality predicate. -/
theorem SourcePsiIntegralModelMinimal_iff
    (M : SourcePsiIntegralModelData S v) :
    SourcePsiIntegralModelMinimal S v M ↔
      ∀ C : VariableChange (SourcePsiCompletionField S v),
        SourcePsiIntegralWeierstrassCurve S v
            (C • (M.curve.map
              (algebraMap (SourcePsiCompletionIntegers S v)
                (SourcePsiCompletionField S v)))) →
          IsCompletionIntegralUnit S v
            (C.u : SourcePsiCompletionField S v) :=
  Iff.rfl
