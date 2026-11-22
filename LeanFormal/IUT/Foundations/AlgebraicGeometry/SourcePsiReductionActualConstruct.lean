/-
  Construction of the reduced special fiber from an actual minimal integral model.

  An actual minimal model is represented by a model together with the corrected
  minimality proof.  From it we construct:
  * the actual reduced Weierstrass curve over the residue field;
  * the actual projective special fiber;
  * the coefficient/discriminant reduction laws and elliptic/singular criteria;
  * the conditional identification with a claimed source special fiber.

  The minimal-model existence itself and the identification with the actual source
  special fiber are recorded as exact residual data.  No model, reduction, or
  special fiber is fabricated.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiMinimalModelUniqueness
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiReductionActualConstruct

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelReduction
open LeanFormal.IUT.SourcePsiMinimalModelUniqueness
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- An actual minimal integral model: an integral model together with the
corrected minimality proof.  No inhabitant is asserted. -/
structure SourcePsiActualMinimalModel where
  model : SourcePsiIntegralModelData S v
  minimal : SourcePsiIntegralModelMinimalCorrected S v model

/-- The constructed reduced curve over the actual residue field. -/
abbrev SourcePsiMinimalReducedCurve
    (A : SourcePsiActualMinimalModel S v) :
    WeierstrassCurve (SourcePsiResidueField S v) :=
  SourcePsiReducedCurve S v A.model

/-- The constructed projective reduced special fiber. -/
abbrev SourcePsiMinimalSpecialFiberProjective
    (A : SourcePsiActualMinimalModel S v) :
    WeierstrassCurve.Projective :=
  (SourcePsiMinimalReducedCurve S v A).toProjective

/-- Construction theorem: the minimal reduced curve is the actual residue map of
the minimal model curve. -/
theorem SourcePsiMinimalReducedCurve_eq_map
    (A : SourcePsiActualMinimalModel S v) :
    SourcePsiMinimalReducedCurve S v A =
      A.model.curve.map (IsLocalRing.residue (SourcePsiCompletionIntegers S v)) :=
  SourcePsiReducedCurve_eq_map S v A.model

/-- Coefficient construction for a1. -/
theorem SourcePsiMinimalReducedCurve_a₁
    (A : SourcePsiActualMinimalModel S v) :
    (SourcePsiMinimalReducedCurve S v A).a₁ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.model.curve.a₁ :=
  SourcePsiReducedCurve_a₁_eq_residue S v A.model

theorem SourcePsiMinimalReducedCurve_a₂
    (A : SourcePsiActualMinimalModel S v) :
    (SourcePsiMinimalReducedCurve S v A).a₂ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.model.curve.a₂ :=
  SourcePsiReducedCurve_a₂_eq_residue S v A.model

theorem SourcePsiMinimalReducedCurve_a₃
    (A : SourcePsiActualMinimalModel S v) :
    (SourcePsiMinimalReducedCurve S v A).a₃ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.model.curve.a₃ :=
  SourcePsiReducedCurve_a₃_eq_residue S v A.model

theorem SourcePsiMinimalReducedCurve_a₄
    (A : SourcePsiActualMinimalModel S v) :
    (SourcePsiMinimalReducedCurve S v A).a₄ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.model.curve.a₄ :=
  SourcePsiReducedCurve_a₄_eq_residue S v A.model

theorem SourcePsiMinimalReducedCurve_a₆
    (A : SourcePsiActualMinimalModel S v) :
    (SourcePsiMinimalReducedCurve S v A).a₆ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.model.curve.a₆ :=
  SourcePsiReducedCurve_a₆_eq_residue S v A.model

/-- Discriminant construction. -/
theorem SourcePsiMinimalReducedCurve_Δ
    (A : SourcePsiActualMinimalModel S v) :
    (SourcePsiMinimalReducedCurve S v A).Δ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.model.curve.Δ :=
  SourcePsiReducedCurve_Δ S v A.model

/-- c4 construction. -/
theorem SourcePsiMinimalReducedCurve_c₄
    (A : SourcePsiActualMinimalModel S v) :
    (SourcePsiMinimalReducedCurve S v A).c₄ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.model.curve.c₄ :=
  SourcePsiReducedCurve_c₄ S v A.model

/-- Reduced discriminant zero iff the integral discriminant lies in the maximal
ideal. -/
theorem SourcePsiMinimalReducedCurve_Δ_eq_zero_iff_mem_maximalIdeal
    (A : SourcePsiActualMinimalModel S v) :
    (SourcePsiMinimalReducedCurve S v A).Δ = 0 ↔
      A.model.curve.Δ ∈
        IsLocalRing.maximalIdeal (SourcePsiCompletionIntegers S v) :=
  SourcePsiReducedCurve_Δ_eq_zero_iff_mem_maximalIdeal S v A.model

/-- Reduced discriminant nonzero iff the integral discriminant is a unit. -/
theorem SourcePsiMinimalReducedCurve_Δ_ne_zero_iff_isUnit
    (A : SourcePsiActualMinimalModel S v) :
    (SourcePsiMinimalReducedCurve S v A).Δ ≠ 0 ↔
      IsUnit A.model.curve.Δ :=
  SourcePsiReducedCurve_Δ_ne_zero_iff_isUnit S v A.model

/-- Elliptic criterion for the minimal reduced curve. -/
theorem SourcePsiMinimalReducedCurve_isElliptic_iff_Δ_ne_zero
    (A : SourcePsiActualMinimalModel S v) :
    (SourcePsiMinimalReducedCurve S v A).IsElliptic ↔
      (SourcePsiMinimalReducedCurve S v A).Δ ≠ 0 :=
  SourcePsiReducedCurve_isElliptic_iff_Δ_ne_zero S v A.model

/-- Elliptic criterion directly on the integral discriminant. -/
theorem SourcePsiMinimalReducedCurve_isElliptic_iff_residue_Δ_ne_zero
    (A : SourcePsiActualMinimalModel S v) :
    (SourcePsiMinimalReducedCurve S v A).IsElliptic ↔
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.model.curve.Δ ≠ 0 := by
  rw [SourcePsiMinimalReducedCurve_isElliptic_iff_Δ_ne_zero S v A,
    SourcePsiMinimalReducedCurve_Δ S v A]

/-- Affine nonsingularity of the minimal reduced curve. -/
theorem SourcePsiMinimalReducedCurve_equation_nonsingular
    (A : SourcePsiActualMinimalModel S v)
    (hΔ : (SourcePsiMinimalReducedCurve S v A).Δ ≠ 0)
    {x y : SourcePsiResidueField S v}
    (hxy : (SourcePsiMinimalReducedCurve S v A).Equation x y) :
    (SourcePsiMinimalReducedCurve S v A).Nonsingular x y :=
  SourcePsiReducedCurve_equation_nonsingular S v A.model hΔ hxy

/-- Elliptic/singular dichotomy for the minimal reduced curve. -/
theorem SourcePsiMinimalReducedCurve_elliptic_or_Δ_zero
    (A : SourcePsiActualMinimalModel S v) :
    (SourcePsiMinimalReducedCurve S v A).IsElliptic ∨
      (SourcePsiMinimalReducedCurve S v A).Δ = 0 :=
  SourcePsiSpecialFiber_elliptic_or_Δ_zero S v A.model

/-- Projective construction: the minimal special fiber is the projective closure
of the minimal reduced curve. -/
theorem SourcePsiMinimalSpecialFiberProjective_eq
    (A : SourcePsiActualMinimalModel S v) :
    SourcePsiMinimalSpecialFiberProjective S v A =
      (SourcePsiMinimalReducedCurve S v A).toProjective := rfl

/-- Actual projective points of the minimal special fiber. -/
abbrev SourcePsiMinimalSpecialFiberProjectivePoint
    (A : SourcePsiActualMinimalModel S v) : Type u :=
  (SourcePsiMinimalSpecialFiberProjective S v A).Point

/-- Actual nonsingular projective points of the minimal special fiber. -/
abbrev SourcePsiMinimalSpecialFiberNonsingularPoint
    (A : SourcePsiActualMinimalModel S v) : Type u :=
  (SourcePsiMinimalSpecialFiberProjective S v A).NonsingularPoint

/-- Conditional identification of a claimed source special fiber with the
constructed minimal reduced curve.  Actual data; no inhabitant is asserted. -/
structure SourcePsiMinimalSpecialFiberIdentification
    (A : SourcePsiActualMinimalModel S v) where
  sourceSpecialFiber : WeierstrassCurve (SourcePsiResidueField S v)
  sourceSpecialFiber_eq_reduced :
    sourceSpecialFiber = SourcePsiMinimalReducedCurve S v A

/-- A reduction identification for the underlying model gives the minimal
special-fiber identification. -/
def SourcePsiMinimalSpecialFiberIdentification.ofReduction
    (A : SourcePsiActualMinimalModel S v)
    (D : SourcePsiReductionIdentification S v A.model) :
    SourcePsiMinimalSpecialFiberIdentification S v A where
  sourceSpecialFiber := D.specialFiber_eq
  sourceSpecialFiber_eq_reduced := D.specialFiber_eq_reduced

/-- The claimed source special fiber equals the constructed minimal reduction. -/
theorem SourcePsiMinimalSpecialFiber_eq_reduced
    (A : SourcePsiActualMinimalModel S v)
    (D : SourcePsiMinimalSpecialFiberIdentification S v A) :
    D.sourceSpecialFiber = SourcePsiMinimalReducedCurve S v A :=
  D.sourceSpecialFiber_eq_reduced

/-- Coefficient comparison for an identified source special fiber. -/
theorem SourcePsiMinimalSpecialFiber_a₁_eq_residue
    (A : SourcePsiActualMinimalModel S v)
    (D : SourcePsiMinimalSpecialFiberIdentification S v A) :
    D.sourceSpecialFiber.a₁ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.model.curve.a₁ := by
  rw [D.sourceSpecialFiber_eq_reduced, SourcePsiMinimalReducedCurve_a₁ S v A]

/-- Discriminant comparison for an identified source special fiber. -/
theorem SourcePsiMinimalSpecialFiber_Δ_eq_residue
    (A : SourcePsiActualMinimalModel S v)
    (D : SourcePsiMinimalSpecialFiberIdentification S v A) :
    D.sourceSpecialFiber.Δ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.model.curve.Δ := by
  rw [D.sourceSpecialFiber_eq_reduced, SourcePsiMinimalReducedCurve_Δ S v A]

/-- Exact residual: an actual minimal model and a source special-fiber
identification.  No inhabitant is asserted. -/
def SourcePsiActualMinimalReductionResidual : Prop :=
  ∃ A : SourcePsiActualMinimalModel S v,
    Nonempty (SourcePsiMinimalSpecialFiberIdentification S v A)



/-- The minimal reduced curve is definitionally the reduced curve of the
underlying integral model. -/
theorem SourcePsiMinimalReducedCurve_independent_of_minimality
    (A : SourcePsiActualMinimalModel S v) :
    SourcePsiMinimalReducedCurve S v A =
      SourcePsiReducedCurve S v A.model := rfl

/-- b2 reduction for the minimal reduced curve. -/
theorem SourcePsiMinimalReducedCurve_b₂
    (A : SourcePsiActualMinimalModel S v) :
    (SourcePsiMinimalReducedCurve S v A).b₂ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.model.curve.b₂ :=
  SourcePsiReducedCurve_b₂ S v A.model

/-- b4 reduction for the minimal reduced curve. -/
theorem SourcePsiMinimalReducedCurve_b₄
    (A : SourcePsiActualMinimalModel S v) :
    (SourcePsiMinimalReducedCurve S v A).b₄ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.model.curve.b₄ :=
  SourcePsiReducedCurve_b₄ S v A.model

/-- b6 reduction for the minimal reduced curve. -/
theorem SourcePsiMinimalReducedCurve_b₆
    (A : SourcePsiActualMinimalModel S v) :
    (SourcePsiMinimalReducedCurve S v A).b₆ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.model.curve.b₆ :=
  SourcePsiReducedCurve_b₆ S v A.model

/-- b8 reduction for the minimal reduced curve. -/
theorem SourcePsiMinimalReducedCurve_b₈
    (A : SourcePsiActualMinimalModel S v) :
    (SourcePsiMinimalReducedCurve S v A).b₈ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.model.curve.b₈ :=
  SourcePsiReducedCurve_b₈ S v A.model

/-- A coefficient comparison for every Weierstrass coefficient of an identified
source special fiber. -/
theorem SourcePsiMinimalSpecialFiber_coefficients_eq_residue
    (A : SourcePsiActualMinimalModel S v)
    (D : SourcePsiMinimalSpecialFiberIdentification S v A) :
    D.sourceSpecialFiber.a₁ =
        IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.model.curve.a₁ ∧
      D.sourceSpecialFiber.a₂ =
        IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.model.curve.a₂ ∧
      D.sourceSpecialFiber.a₃ =
        IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.model.curve.a₃ ∧
      D.sourceSpecialFiber.a₄ =
        IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.model.curve.a₄ ∧
      D.sourceSpecialFiber.a₆ =
        IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.model.curve.a₆ := by
  rw [D.sourceSpecialFiber_eq_reduced]
  exact ⟨SourcePsiMinimalReducedCurve_a₁ S v A,
    SourcePsiMinimalReducedCurve_a₂ S v A,
    SourcePsiMinimalReducedCurve_a₃ S v A,
    SourcePsiMinimalReducedCurve_a₄ S v A,
    SourcePsiMinimalReducedCurve_a₆ S v A⟩

/-- Identification of the projective special fiber. -/
theorem SourcePsiMinimalSpecialFiberProjective_identifies_reduced
    (A : SourcePsiActualMinimalModel S v) :
    SourcePsiMinimalSpecialFiberProjective S v A =
      (SourcePsiReducedCurve S v A.model).toProjective :=
  SourcePsiMinimalSpecialFiberProjective_eq S v A

/-- An identified source special fiber is nonelliptic exactly when its
discriminant vanishes, via the reduced curve. -/
theorem SourcePsiMinimalSpecialFiber_isElliptic_iff_Δ_ne_zero
    (A : SourcePsiActualMinimalModel S v)
    (D : SourcePsiMinimalSpecialFiberIdentification S v A) :
    D.sourceSpecialFiber.IsElliptic ↔
      D.sourceSpecialFiber.Δ ≠ 0 := by
  rw [D.sourceSpecialFiber_eq_reduced]
  exact SourcePsiMinimalReducedCurve_isElliptic_iff_Δ_ne_zero S v A

/-! ## Exact construction boundary

Constructed conditionally from an actual minimal model:
- the reduced curve over the actual residue field;
- all five coefficient reductions and the discriminant/c4 reductions;
- the elliptic/nonsingular criterion and the elliptic/singular dichotomy;
- the projective special fiber and its points;
- the conditional source special-fiber identification and its coefficient/
  discriminant comparisons.

NOT constructed or asserted:
1. an actual minimal model (SourcePsiActualMinimalModel has no fabricated
   inhabitant);
2. an actual source special fiber beyond the equality datum;
3. properness/regularity of the model or special fiber;
4. component/node data and stable reduction type;
5. a proof that the reduced special fiber is the actual source special fiber.

These are exact residual objects.  No reduction or special fiber is fabricated.
-/
end LeanFormal.IUT.SourcePsiReductionActualConstruct

end