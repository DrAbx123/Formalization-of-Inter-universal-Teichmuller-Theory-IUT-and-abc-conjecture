/-
  Comparison of the actual Mathlib minimal special fiber with source special-fiber
  data from Definition 3.1.

  The actual object is (W.minimal R).reduction R, with W the source base-changed
  curve.  Definition 3.1 supplies abstract reduction clauses (stable, multiplicative,
  split multiplicative, q-parameter) but not an actual Weierstrass special fiber over
  the completion residue field.  We therefore take as comparison datum an actual
  source curve over that residue field together with the exact coefficient equality
  to the Mathlib reduction.  From that datum we prove coefficient, discriminant,
  c4 and elliptic agreement.

  No source identification is invented: the comparison datum has no fabricated
  inhabitant, and the missing proper/regular/component/stable comparison is stated
  explicitly as residual.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiActualSpecialFiber
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiSourceSpecialFiberComparison

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelReduction
open LeanFormal.IUT.SourcePsiReductionSpecialFiber
open LeanFormal.IUT.SourcePsiActualSpecialFiber
open LeanFormal.IUT.SourcePsiActualMinimalSpecialFiber
open LeanFormal.IUT.SourcePsiResidueRingFinite
open LeanFormal.IUT.AdicCompletionFractionField
open LeanFormal.IUT.SourcePsiMinimalModelCriterion
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- Actual Mathlib minimal special fiber over the completion residue field. -/
abbrev SourcePsiComparisonActualFiber :
    WeierstrassCurve (SourcePsiResidueField S v) :=
  SourcePsiActualSpecialFiber S v

/-- Actual Mathlib minimal integral curve over the completion integers. -/
abbrev SourcePsiComparisonIntegralCurve :
    WeierstrassCurve (SourcePsiMathlibMinimalBaseRing S v) :=
  SourcePsiActualMinimalIntegralCurve S v

/-- Actual source-base minimal curve over the completion field. -/
abbrev SourcePsiComparisonMinimalCurve :
    WeierstrassCurve (SourcePsiMathlibMinimalFractionField S v) :=
  SourcePsiActualMinimalBaseCurve S v

/-- A source special-fiber comparison datum: an actual curve over the completion
residue field together with its exact equality to the Mathlib reduction.  This is
a comparison hypothesis, not a fabricated source object. -/
structure SourcePsiSourceSpecialFiberComparison where
  place : S.selectedPlaces
  sourceCurve : WeierstrassCurve (SourcePsiResidueField S v)
  sourceCurve_eq_actual : sourceCurve = SourcePsiComparisonActualFiber S v

/-- The compared source curve has the same coefficients as the Mathlib minimal
special fiber. -/
theorem SourcePsiSourceSpecialFiberComparison_a₁
    (D : SourcePsiSourceSpecialFiberComparison S v) :
    D.sourceCurve.a₁ = (SourcePsiComparisonActualFiber S v).a₁ :=
  congrArg WeierstrassCurve.a₁ D.sourceCurve_eq_actual

theorem SourcePsiSourceSpecialFiberComparison_a₂
    (D : SourcePsiSourceSpecialFiberComparison S v) :
    D.sourceCurve.a₂ = (SourcePsiComparisonActualFiber S v).a₂ :=
  congrArg WeierstrassCurve.a₂ D.sourceCurve_eq_actual

theorem SourcePsiSourceSpecialFiberComparison_a₃
    (D : SourcePsiSourceSpecialFiberComparison S v) :
    D.sourceCurve.a₃ = (SourcePsiComparisonActualFiber S v).a₃ :=
  congrArg WeierstrassCurve.a₃ D.sourceCurve_eq_actual

theorem SourcePsiSourceSpecialFiberComparison_a₄
    (D : SourcePsiSourceSpecialFiberComparison S v) :
    D.sourceCurve.a₄ = (SourcePsiComparisonActualFiber S v).a₄ :=
  congrArg WeierstrassCurve.a₄ D.sourceCurve_eq_actual

theorem SourcePsiSourceSpecialFiberComparison_a₆
    (D : SourcePsiSourceSpecialFiberComparison S v) :
    D.sourceCurve.a₆ = (SourcePsiComparisonActualFiber S v).a₆ :=
  congrArg WeierstrassCurve.a₆ D.sourceCurve_eq_actual

/-- All five coefficient comparisons at once. -/
theorem SourcePsiSourceSpecialFiberComparison_coefficients
    (D : SourcePsiSourceSpecialFiberComparison S v) :
    D.sourceCurve.a₁ = (SourcePsiComparisonActualFiber S v).a₁ ∧
      D.sourceCurve.a₂ = (SourcePsiComparisonActualFiber S v).a₂ ∧
      D.sourceCurve.a₃ = (SourcePsiComparisonActualFiber S v).a₃ ∧
      D.sourceCurve.a₄ = (SourcePsiComparisonActualFiber S v).a₄ ∧
      D.sourceCurve.a₆ = (SourcePsiComparisonActualFiber S v).a₆ :=
  ⟨SourcePsiSourceSpecialFiberComparison_a₁ S v D,
    SourcePsiSourceSpecialFiberComparison_a₂ S v D,
    SourcePsiSourceSpecialFiberComparison_a₃ S v D,
    SourcePsiSourceSpecialFiberComparison_a₄ S v D,
    SourcePsiSourceSpecialFiberComparison_a₆ S v D⟩

/-- Discriminant comparison with the Mathlib minimal special fiber. -/
theorem SourcePsiSourceSpecialFiberComparison_Δ
    (D : SourcePsiSourceSpecialFiberComparison S v) :
    D.sourceCurve.Δ = (SourcePsiComparisonActualFiber S v).Δ :=
  congrArg WeierstrassCurve.Δ D.sourceCurve_eq_actual

/-- c4 comparison with the Mathlib minimal special fiber. -/
theorem SourcePsiSourceSpecialFiberComparison_c₄
    (D : SourcePsiSourceSpecialFiberComparison S v) :
    D.sourceCurve.c₄ = (SourcePsiComparisonActualFiber S v).c₄ :=
  congrArg WeierstrassCurve.c₄ D.sourceCurve_eq_actual

/-- c6 comparison with the Mathlib minimal special fiber. -/
theorem SourcePsiSourceSpecialFiberComparison_c₆
    (D : SourcePsiSourceSpecialFiberComparison S v) :
    D.sourceCurve.c₆ = (SourcePsiComparisonActualFiber S v).c₆ :=
  congrArg WeierstrassCurve.c₆ D.sourceCurve_eq_actual

/-- Elliptic agreement for a compared source special fiber. -/
theorem SourcePsiSourceSpecialFiberComparison_isElliptic_iff
    (D : SourcePsiSourceSpecialFiberComparison S v) :
    D.sourceCurve.IsElliptic ↔ (SourcePsiComparisonActualFiber S v).IsElliptic := by
  rw [D.sourceCurve_eq_actual]

/-- Elliptic agreement with actual good reduction. -/
theorem SourcePsiSourceSpecialFiberComparison_isElliptic_iff_goodReduction
    (D : SourcePsiSourceSpecialFiberComparison S v) :
    D.sourceCurve.IsElliptic ↔ SourcePsiActualGoodReduction S v :=
  (SourcePsiSourceSpecialFiberComparison_isElliptic_iff S v D).trans
    (SourcePsiActualSpecialFiber_goodReduction_iff_isElliptic S v).symm

/-- Singular agreement: the source curve is singular iff the actual residue
discriminant vanishes. -/
theorem SourcePsiSourceSpecialFiberComparison_not_isElliptic_iff_Δ_eq_zero
    (D : SourcePsiSourceSpecialFiberComparison S v) :
    ¬ D.sourceCurve.IsElliptic ↔ (SourcePsiComparisonActualFiber S v).Δ = 0 := by
  rw [SourcePsiSourceSpecialFiberComparison_isElliptic_iff S v D]
  exact SourcePsiActualSpecialFiber_not_isElliptic_iff_Δ_eq_zero S v

/-- Source curve discriminant agreement under the comparison. -/
theorem SourcePsiSourceSpecialFiberComparison_Δ_eq_zero_iff
    (D : SourcePsiSourceSpecialFiberComparison S v) :
    D.sourceCurve.Δ = 0 ↔ (SourcePsiComparisonActualFiber S v).Δ = 0 := by
  rw [SourcePsiSourceSpecialFiberComparison_Δ S v D]

/-- Actual Mathlib special fiber equals the reduced curve of the actual minimal
model. -/
theorem SourcePsiComparisonActualFiber_eq_reducedCurve :
    SourcePsiComparisonActualFiber S v =
      SourcePsiMathlibMinimalReducedCurve S v :=
  SourcePsiActualSpecialFiber_eq_reducedCurve S v

/-- Definition 3.1 stable reduction clause for a bad place. -/
abbrev SourcePsiDefinition31StableReduction (b : S.badPlaces) : Prop :=
  S.reduction.stableReduction b

/-- Definition 3.1 multiplicative reduction clause for a bad place. -/
abbrev SourcePsiDefinition31MultiplicativeReduction (b : S.badPlaces) : Prop :=
  S.reduction.multiplicativeReduction b

/-- Definition 3.1 split multiplicative reduction clause for a bad place. -/
abbrev SourcePsiDefinition31SplitMultiplicativeReduction (b : S.badPlaces) : Prop :=
  S.reduction.splitMultiplicativeReduction b

/-- The source stable reduction Prop holds for every bad place (Definition 3.1). -/
theorem SourcePsiDefinition31StableReduction_proved (b : S.badPlaces) :
    SourcePsiDefinition31StableReduction S b :=
  S.reduction.stableReduction_proved b

/-- The source multiplicative reduction Prop holds for every bad place. -/
theorem SourcePsiDefinition31MultiplicativeReduction_proved (b : S.badPlaces) :
    SourcePsiDefinition31MultiplicativeReduction S b :=
  S.reduction.multiplicativeReduction_proved b

/-- The source split multiplicative reduction Prop holds for every bad place. -/
theorem SourcePsiDefinition31SplitMultiplicativeReduction_proved (b : S.badPlaces) :
    SourcePsiDefinition31SplitMultiplicativeReduction S b :=
  S.reduction.splitMultiplicativeReduction_proved b

/-- Abstract source reduction type data at a bad place.  This is Definition 3.1
data only; it does not identify the place with the actual completion place. -/
structure SourcePsiDefinition31ReductionTypeData (b : S.badPlaces) where
  stable : SourcePsiDefinition31StableReduction S b
  multiplicative : SourcePsiDefinition31MultiplicativeReduction S b
  splitMultiplicative : SourcePsiDefinition31SplitMultiplicativeReduction S b

/-- The source reduction type data at every bad place. -/
def SourcePsiDefinition31ReductionTypeData.ofBadPlace (b : S.badPlaces) :
    SourcePsiDefinition31ReductionTypeData S b where
  stable := SourcePsiDefinition31StableReduction_proved S b
  multiplicative := SourcePsiDefinition31MultiplicativeReduction_proved S b
  splitMultiplicative := SourcePsiDefinition31SplitMultiplicativeReduction_proved S b

/-- Exact comparison residual: a source special-fiber comparison datum and a
correspondence between a Definition 3.1 bad place and the actual completion
place.  No inhabitant is asserted. -/
def SourcePsiSourceSpecialFiberComparisonResidual : Prop :=
  (∃ D : SourcePsiSourceSpecialFiberComparison S v,
    D.sourceCurve = SourcePsiComparisonActualFiber S v) ∧
    ∃ b : S.badPlaces,
      Nonempty (SourcePsiDefinition31ReductionTypeData S b)



/-- b2 comparison with the Mathlib minimal special fiber. -/
theorem SourcePsiSourceSpecialFiberComparison_b₂
    (D : SourcePsiSourceSpecialFiberComparison S v) :
    D.sourceCurve.b₂ = (SourcePsiComparisonActualFiber S v).b₂ :=
  congrArg WeierstrassCurve.b₂ D.sourceCurve_eq_actual

/-- b4 comparison. -/
theorem SourcePsiSourceSpecialFiberComparison_b₄
    (D : SourcePsiSourceSpecialFiberComparison S v) :
    D.sourceCurve.b₄ = (SourcePsiComparisonActualFiber S v).b₄ :=
  congrArg WeierstrassCurve.b₄ D.sourceCurve_eq_actual

/-- b6 comparison. -/
theorem SourcePsiSourceSpecialFiberComparison_b₆
    (D : SourcePsiSourceSpecialFiberComparison S v) :
    D.sourceCurve.b₆ = (SourcePsiComparisonActualFiber S v).b₆ :=
  congrArg WeierstrassCurve.b₆ D.sourceCurve_eq_actual

/-- b8 comparison. -/
theorem SourcePsiSourceSpecialFiberComparison_b₈
    (D : SourcePsiSourceSpecialFiberComparison S v) :
    D.sourceCurve.b₈ = (SourcePsiComparisonActualFiber S v).b₈ :=
  congrArg WeierstrassCurve.b₈ D.sourceCurve_eq_actual

/-- Nonzero source discriminant iff nonzero Mathlib special-fiber discriminant. -/
theorem SourcePsiSourceSpecialFiberComparison_Δ_ne_zero_iff
    (D : SourcePsiSourceSpecialFiberComparison S v) :
    D.sourceCurve.Δ ≠ 0 ↔ (SourcePsiComparisonActualFiber S v).Δ ≠ 0 := by
  rw [SourcePsiSourceSpecialFiberComparison_Δ S v D]

/-- Elliptic source comparison gives actual good reduction. -/
theorem SourcePsiSourceSpecialFiberComparison_goodReduction_of_isElliptic
    (D : SourcePsiSourceSpecialFiberComparison S v)
    (h : D.sourceCurve.IsElliptic) :
    SourcePsiActualGoodReduction S v :=
  (SourcePsiSourceSpecialFiberComparison_isElliptic_iff_goodReduction S v D).mp h

/-- Actual good reduction gives an elliptic source comparison. -/
theorem SourcePsiSourceSpecialFiberComparison_isElliptic_of_goodReduction
    (D : SourcePsiSourceSpecialFiberComparison S v)
    (h : SourcePsiActualGoodReduction S v) :
    D.sourceCurve.IsElliptic :=
  (SourcePsiSourceSpecialFiberComparison_isElliptic_iff_goodReduction S v D).mpr h

/-- Definition 3.1 q-parameter is nonzero at every bad place. -/
theorem SourcePsiDefinition31_qParameter_nonzero (b : S.badPlaces) :
    S.reduction.qParameter b ≠ 0 :=
  S.reduction.qParameter_nonzero b

/-- Definition 3.1 q-parameter is contracting at every bad place. -/
theorem SourcePsiDefinition31_qParameter_contracting (b : S.badPlaces) :
    ‖S.reduction.qParameter b‖ < 1 :=
  S.reduction.qParameter_contracting b

/-- Definition 3.1 split multiplicative implies multiplicative. -/
theorem SourcePsiDefinition31_split_imp_multiplicative (b : S.badPlaces)
    (h : SourcePsiDefinition31SplitMultiplicativeReduction S b) :
    SourcePsiDefinition31MultiplicativeReduction S b :=
  S.reduction.reductionCompatibility b h



/-- The source comparison curve is exactly the actual Mathlib special fiber. -/
theorem SourcePsiSourceSpecialFiberComparison_curve_eq
    (D : SourcePsiSourceSpecialFiberComparison S v) :
    D.sourceCurve = SourcePsiComparisonActualFiber S v :=
  D.sourceCurve_eq_actual

/-! ## Exact source comparison boundary

Proved conditionally on a source comparison datum:
- all five coefficient comparisons with the Mathlib minimal special fiber;
- discriminant, c4, c6 comparisons;
- elliptic agreement, and elliptic iff actual good reduction;
- singular iff actual residue discriminant zero;
- actual special fiber equals the reduced curve of the actual minimal model;
- Definition 3.1 stable/multiplicative/split multiplicative clauses hold at every
  bad place, and their reduction-type data is packaged.

NOT constructed or asserted:
1. a source special fiber curve over the completion residue field beyond the
   comparison datum (no fabricated inhabitant);
2. a correspondence between a Definition 3.1 bad place and the actual completion
   place v;
3. properness/regularity of the actual integral minimal model;
4. component/node graph or stable/split comparison in the source sense;
5. an actual source identification beyond the equality datum.

These are exact residual objects.  No source identification is fabricated.
-/
end LeanFormal.IUT.SourcePsiSourceSpecialFiberComparison

end