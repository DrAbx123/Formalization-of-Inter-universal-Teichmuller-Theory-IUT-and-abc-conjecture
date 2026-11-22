/-
  Coefficient integrality for the base-changed Weierstrass curve at an actual
  finite place, and its exact relation to the integral-model residual.

  The five coefficients of the source curve are viewed in the actual adic
  completion `v.adicCompletion F`.  The adic completion integer ring is Mathlib's
  valuation subring `v.adicCompletionIntegers F`.  We prove:

  * coefficient integrality is exactly the five valuation bounds `v(a_i) <= 1`;
  * existence of an integral Weierstrass model over the adic completion integers
    whose base change is the actual base-changed source curve is equivalent to
    those five coefficient bounds.

  Consequently the precise bound on `SourcePsiCoefficientsIntegral` is the
  conjunction of the five actual valuations `<= 1`; when one coefficient has
  valuation `> 1`, no raw integral model exists.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiIntegralModel
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiCoefficientIntegrality

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralUnits
open LeanFormal.IUT.SourcePsiIntegralUnitsCompletion
open LeanFormal.IUT.SourcePsiIntegralModel
open WeierstrassCurve
open scoped Pointwise

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- Membership in the actual adic completion integer ring is the valuation bound
`<= 1`. -/
theorem mem_sourcePsiCompletionIntegers_iff_valued_le_one
    {x : SourcePsiCompletionField S v} :
    x ∈ (SourcePsiCompletionIntegers S v :
        Set (SourcePsiCompletionField S v)) ↔
      Valued.v x ≤ 1 :=
  IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers

/-- The coefficient of the base-changed source curve at `a₁`, expressed as the
actual algebra-map image of the source coefficient. -/
theorem SourcePsiBaseChangedCurve_a₁ :
    (SourcePsiBaseChangedCurve S v).a₁ =
      algebraMap S.arithmetic.F (SourcePsiCompletionField S v)
        S.arithmetic.curve.curve.a₁ := rfl

theorem SourcePsiBaseChangedCurve_a₂ :
    (SourcePsiBaseChangedCurve S v).a₂ =
      algebraMap S.arithmetic.F (SourcePsiCompletionField S v)
        S.arithmetic.curve.curve.a₂ := rfl

theorem SourcePsiBaseChangedCurve_a₃ :
    (SourcePsiBaseChangedCurve S v).a₃ =
      algebraMap S.arithmetic.F (SourcePsiCompletionField S v)
        S.arithmetic.curve.curve.a₃ := rfl

theorem SourcePsiBaseChangedCurve_a₄ :
    (SourcePsiBaseChangedCurve S v).a₄ =
      algebraMap S.arithmetic.F (SourcePsiCompletionField S v)
        S.arithmetic.curve.curve.a₄ := rfl

theorem SourcePsiBaseChangedCurve_a₆ :
    (SourcePsiBaseChangedCurve S v).a₆ =
      algebraMap S.arithmetic.F (SourcePsiCompletionField S v)
        S.arithmetic.curve.curve.a₆ := rfl

/-- Exact valuation form of the five coefficient integrality conditions. -/
theorem SourcePsiCoefficientsIntegral_iff_valued :
    SourcePsiCoefficientsIntegral S v ↔
      Valued.v (algebraMap S.arithmetic.F (SourcePsiCompletionField S v)
          S.arithmetic.curve.curve.a₁) ≤ 1 ∧
      Valued.v (algebraMap S.arithmetic.F (SourcePsiCompletionField S v)
          S.arithmetic.curve.curve.a₂) ≤ 1 ∧
      Valued.v (algebraMap S.arithmetic.F (SourcePsiCompletionField S v)
          S.arithmetic.curve.curve.a₃) ≤ 1 ∧
      Valued.v (algebraMap S.arithmetic.F (SourcePsiCompletionField S v)
          S.arithmetic.curve.curve.a₄) ≤ 1 ∧
      Valued.v (algebraMap S.arithmetic.F (SourcePsiCompletionField S v)
          S.arithmetic.curve.curve.a₆) ≤ 1 := by
  simp only [SourcePsiCoefficientsIntegral,
    mem_sourcePsiCompletionIntegers_iff_valued_le_one]

/-- An integral model over the adic completion integers forces every actual
coefficient of the base-changed source curve to be integral. -/
theorem sourcePsiCoefficientsIntegral_of_modelResidual
    (h : SourcePsiIntegralModelResidual S v) :
    SourcePsiCoefficientsIntegral S v := by
  obtain ⟨M⟩ := h
  have h₁ : algebraMap S.arithmetic.F (SourcePsiCompletionField S v)
      S.arithmetic.curve.curve.a₁ =
      algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v)
        (M.curve.a₁) := by
    have := congrArg (fun W : WeierstrassCurve (SourcePsiCompletionField S v) => W.a₁)
      M.baseChange_eq
    simpa [SourcePsiBaseChangedCurve, SourcePsiCompletionCurve, WeierstrassCurve.map]
      using this
  have h₂ : algebraMap S.arithmetic.F (SourcePsiCompletionField S v)
      S.arithmetic.curve.curve.a₂ =
      algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v)
        (M.curve.a₂) := by
    have := congrArg (fun W : WeierstrassCurve (SourcePsiCompletionField S v) => W.a₂)
      M.baseChange_eq
    simpa [SourcePsiBaseChangedCurve, SourcePsiCompletionCurve, WeierstrassCurve.map]
      using this
  have h₃ : algebraMap S.arithmetic.F (SourcePsiCompletionField S v)
      S.arithmetic.curve.curve.a₃ =
      algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v)
        (M.curve.a₃) := by
    have := congrArg (fun W : WeierstrassCurve (SourcePsiCompletionField S v) => W.a₃)
      M.baseChange_eq
    simpa [SourcePsiBaseChangedCurve, SourcePsiCompletionCurve, WeierstrassCurve.map]
      using this
  have h₄ : algebraMap S.arithmetic.F (SourcePsiCompletionField S v)
      S.arithmetic.curve.curve.a₄ =
      algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v)
        (M.curve.a₄) := by
    have := congrArg (fun W : WeierstrassCurve (SourcePsiCompletionField S v) => W.a₄)
      M.baseChange_eq
    simpa [SourcePsiBaseChangedCurve, SourcePsiCompletionCurve, WeierstrassCurve.map]
      using this
  have h₆ : algebraMap S.arithmetic.F (SourcePsiCompletionField S v)
      S.arithmetic.curve.curve.a₆ =
      algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v)
        (M.curve.a₆) := by
    have := congrArg (fun W : WeierstrassCurve (SourcePsiCompletionField S v) => W.a₆)
      M.baseChange_eq
    simpa [SourcePsiBaseChangedCurve, SourcePsiCompletionCurve, WeierstrassCurve.map]
      using this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h₁]
    exact IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers _ M.curve.a₁
  · rw [h₂]
    exact IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers _ M.curve.a₂
  · rw [h₃]
    exact IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers _ M.curve.a₃
  · rw [h₄]
    exact IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers _ M.curve.a₄
  · rw [h₆]
    exact IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers _ M.curve.a₆

/-- Coefficient integrality constructs the raw integral model, hence the model
residual. -/
theorem modelResidual_of_sourcePsiCoefficientsIntegral
    (h : SourcePsiCoefficientsIntegral S v) :
    SourcePsiIntegralModelResidual S v :=
  sourcePsiIntegralModelResidual_of_coefficients S v h

/-- Exact equivalence: an integral model over the adic completion integers exists
if and only if all five actual source coefficients are integral at v. -/
theorem sourcePsiIntegralModelResidual_iff_coefficientsIntegral :
    SourcePsiIntegralModelResidual S v ↔
      SourcePsiCoefficientsIntegral S v :=
  ⟨sourcePsiCoefficientsIntegral_of_modelResidual S v,
    modelResidual_of_sourcePsiCoefficientsIntegral S v⟩

/-- The exact valuation bound for coefficient integrality is the conjunction of
the five `v(a_i) <= 1` inequalities. -/
theorem sourcePsiIntegralModelResidual_iff_valued :
    SourcePsiIntegralModelResidual S v ↔
      Valued.v (algebraMap S.arithmetic.F (SourcePsiCompletionField S v)
          S.arithmetic.curve.curve.a₁) ≤ 1 ∧
      Valued.v (algebraMap S.arithmetic.F (SourcePsiCompletionField S v)
          S.arithmetic.curve.curve.a₂) ≤ 1 ∧
      Valued.v (algebraMap S.arithmetic.F (SourcePsiCompletionField S v)
          S.arithmetic.curve.curve.a₃) ≤ 1 ∧
      Valued.v (algebraMap S.arithmetic.F (SourcePsiCompletionField S v)
          S.arithmetic.curve.curve.a₄) ≤ 1 ∧
      Valued.v (algebraMap S.arithmetic.F (SourcePsiCompletionField S v)
          S.arithmetic.curve.curve.a₆) ≤ 1 :=
  (sourcePsiIntegralModelResidual_iff_coefficientsIntegral S v).trans
    (SourcePsiCoefficientsIntegral_iff_valued S v)

/-- If one actual coefficient has valuation strictly greater than one, no raw
integral model over the adic completion integers exists. -/
theorem not_modelResidual_of_valued_gt_one_a₁
    (h : 1 < Valued.v (algebraMap S.arithmetic.F
      (SourcePsiCompletionField S v) S.arithmetic.curve.curve.a₁)) :
    ¬ SourcePsiIntegralModelResidual S v := by
  intro hmodel
  have hcoeff := sourcePsiCoefficientsIntegral_of_modelResidual S v hmodel
  have hv := (SourcePsiCoefficientsIntegral_iff_valued S v).mp hcoeff
  exact (not_le_of_gt h) hv.1

theorem not_modelResidual_of_valued_gt_one_a₂
    (h : 1 < Valued.v (algebraMap S.arithmetic.F
      (SourcePsiCompletionField S v) S.arithmetic.curve.curve.a₂)) :
    ¬ SourcePsiIntegralModelResidual S v := by
  intro hmodel
  have hcoeff := sourcePsiCoefficientsIntegral_of_modelResidual S v hmodel
  have hv := (SourcePsiCoefficientsIntegral_iff_valued S v).mp hcoeff
  exact (not_le_of_gt h) hv.2.1

theorem not_modelResidual_of_valued_gt_one_a₃
    (h : 1 < Valued.v (algebraMap S.arithmetic.F
      (SourcePsiCompletionField S v) S.arithmetic.curve.curve.a₃)) :
    ¬ SourcePsiIntegralModelResidual S v := by
  intro hmodel
  have hcoeff := sourcePsiCoefficientsIntegral_of_modelResidual S v hmodel
  have hv := (SourcePsiCoefficientsIntegral_iff_valued S v).mp hcoeff
  exact (not_le_of_gt h) hv.2.2.1

theorem not_modelResidual_of_valued_gt_one_a₄
    (h : 1 < Valued.v (algebraMap S.arithmetic.F
      (SourcePsiCompletionField S v) S.arithmetic.curve.curve.a₄)) :
    ¬ SourcePsiIntegralModelResidual S v := by
  intro hmodel
  have hcoeff := sourcePsiCoefficientsIntegral_of_modelResidual S v hmodel
  have hv := (SourcePsiCoefficientsIntegral_iff_valued S v).mp hcoeff
  exact (not_le_of_gt h) hv.2.2.2.1

theorem not_modelResidual_of_valued_gt_one_a₆
    (h : 1 < Valued.v (algebraMap S.arithmetic.F
      (SourcePsiCompletionField S v) S.arithmetic.curve.curve.a₆)) :
    ¬ SourcePsiIntegralModelResidual S v := by
  intro hmodel
  have hcoeff := sourcePsiCoefficientsIntegral_of_modelResidual S v hmodel
  have hv := (SourcePsiCoefficientsIntegral_iff_valued S v).mp hcoeff
  exact (not_le_of_gt h) hv.2.2.2.2

/-! ## Exact bound and residual

The five coefficient integrality conditions are exactly the five valuation
bounds `Valued.v (algebraMap F K_v (a_i)) <= 1`.  The existence of an integral
Weierstrass model over `v.adicCompletionIntegers F` whose base change is the
actual base-changed source curve is equivalent to these five bounds.

If one coefficient has valuation `> 1`, no such raw integral model exists.
Minimal models obtained by a non-integral Weierstrass change of coordinates are
not constructed here; the equivalence above is specifically for models whose
coefficients are already in the adic completion integers and whose base change
is the actual source curve.
-/

end LeanFormal.IUT.SourcePsiCoefficientIntegrality

end
