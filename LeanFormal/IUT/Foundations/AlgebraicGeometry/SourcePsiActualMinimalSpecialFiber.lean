/-
  The actual minimal special fiber from Mathlib's minimal Weierstrass model.

  Mathlib's reduction theory supplies:
  * W.minimal R, a minimal Weierstrass equation for a curve over the fraction
    field K;
  * integralModel R (W.minimal R), its integral Weierstrass curve over R;
  * (W.minimal R).reduction R, the actual reduced curve over the residue field;
  * good-reduction/elliptic criteria and multiplicative/additive reduction
    predicates.

  This file applies these actual objects to the source base-changed curve, proves
  the special-fiber equality with Mathlib's reduction, the coefficient and
  discriminant reduction laws, and the elliptic/singular dichotomy from the
  residue discriminant.  No special fiber, model, or reduction is fabricated.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiReductionActualConstruct
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiResidueRingFinite
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiActualMinimalSpecialFiber

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelReduction
open LeanFormal.IUT.SourcePsiReductionSpecialFiber
open LeanFormal.IUT.SourcePsiReductionActualConstruct
open LeanFormal.IUT.SourcePsiResidueRingFinite
open LeanFormal.IUT.AdicCompletionFractionField
open LeanFormal.IUT.SourcePsiMinimalModelCriterion
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- The actual DVR of the adic completion integers. -/
abbrev SourcePsiMathlibMinimalBaseRing : Type u :=
  v.adicCompletionIntegers S.arithmetic.F

/-- The actual fraction field of the adic completion integers. -/
abbrev SourcePsiMathlibMinimalFractionField : Type u :=
  v.adicCompletion S.arithmetic.F

/-- The actual source base-changed Weierstrass curve over K. -/
abbrev SourcePsiMathlibMinimalBaseCurve :
    WeierstrassCurve (SourcePsiMathlibMinimalFractionField S v) :=
  SourcePsiBaseChangedCurve S v

/-- Mathlib's actual minimal Weierstrass model of the source base-changed curve. -/
noncomputable def SourcePsiMathlibMinimalCurve :
    WeierstrassCurve (SourcePsiMathlibMinimalFractionField S v) :=
  (SourcePsiMathlibMinimalBaseCurve S v).minimal
    (SourcePsiMathlibMinimalBaseRing S v)

/-- The actual minimal model is integral. -/
theorem SourcePsiMathlibMinimalCurve_isIntegral :
    IsIntegral (SourcePsiMathlibMinimalBaseRing S v)
      (SourcePsiMathlibMinimalCurve S v) :=
  inferInstance

/-- The actual minimal model is minimal. -/
theorem SourcePsiMathlibMinimalCurve_isMinimal :
    IsMinimal (SourcePsiMathlibMinimalBaseRing S v)
      (SourcePsiMathlibMinimalCurve S v) :=
  inferInstance

/-- The actual integral Weierstrass model attached to the Mathlib minimal
model. -/
noncomputable def SourcePsiMathlibMinimalIntegralCurve :
    WeierstrassCurve (SourcePsiMathlibMinimalBaseRing S v) :=
  integralModel (SourcePsiMathlibMinimalBaseRing S v)
    (SourcePsiMathlibMinimalCurve S v)

/-- The actual integral model base-changes to the Mathlib minimal curve. -/
theorem SourcePsiMathlibMinimalIntegralCurve_baseChange :
    (SourcePsiMathlibMinimalIntegralCurve S v).map
      (algebraMap (SourcePsiMathlibMinimalBaseRing S v)
        (SourcePsiMathlibMinimalFractionField S v)) =
      SourcePsiMathlibMinimalCurve S v :=
  WeierstrassCurve.baseChange_integralModel_eq
    (SourcePsiMathlibMinimalBaseRing S v) (SourcePsiMathlibMinimalCurve S v)

/-- The actual minimal special fiber: Mathlib's reduction of the minimal
model. -/
noncomputable def SourcePsiMathlibMinimalSpecialFiber :
    WeierstrassCurve (SourcePsiResidueField S v) :=
  (SourcePsiMathlibMinimalCurve S v).reduction
    (SourcePsiMathlibMinimalBaseRing S v)

/-- The reduced curve of the actual minimal model, i.e. the residue map of the
integral minimal model. -/
noncomputable def SourcePsiMathlibMinimalReducedCurve :
    WeierstrassCurve (SourcePsiResidueField S v) :=
  (SourcePsiMathlibMinimalIntegralCurve S v).map
    (IsLocalRing.residue (SourcePsiMathlibMinimalBaseRing S v))

/-- Actual special-fiber identification: Mathlib's reduction equals the residue
map of the actual minimal integral model. -/
theorem SourcePsiMathlibMinimalSpecialFiber_eq_reducedCurve :
    SourcePsiMathlibMinimalSpecialFiber S v =
      SourcePsiMathlibMinimalReducedCurve S v := rfl

/-- Coefficient law a1 for the actual minimal special fiber. -/
theorem SourcePsiMathlibMinimalSpecialFiber_a₁ :
    (SourcePsiMathlibMinimalSpecialFiber S v).a₁ =
      IsLocalRing.residue (SourcePsiMathlibMinimalBaseRing S v)
        (SourcePsiMathlibMinimalIntegralCurve S v).a₁ := by
  rw [SourcePsiMathlibMinimalSpecialFiber,
    SourcePsiMathlibMinimalReducedCurve,
    WeierstrassCurve.reduction, WeierstrassCurve.map_a₁]

theorem SourcePsiMathlibMinimalSpecialFiber_a₂ :
    (SourcePsiMathlibMinimalSpecialFiber S v).a₂ =
      IsLocalRing.residue (SourcePsiMathlibMinimalBaseRing S v)
        (SourcePsiMathlibMinimalIntegralCurve S v).a₂ := by
  rw [SourcePsiMathlibMinimalSpecialFiber,
    SourcePsiMathlibMinimalReducedCurve,
    WeierstrassCurve.reduction, WeierstrassCurve.map_a₂]

theorem SourcePsiMathlibMinimalSpecialFiber_a₃ :
    (SourcePsiMathlibMinimalSpecialFiber S v).a₃ =
      IsLocalRing.residue (SourcePsiMathlibMinimalBaseRing S v)
        (SourcePsiMathlibMinimalIntegralCurve S v).a₃ := by
  rw [SourcePsiMathlibMinimalSpecialFiber,
    SourcePsiMathlibMinimalReducedCurve,
    WeierstrassCurve.reduction, WeierstrassCurve.map_a₃]

theorem SourcePsiMathlibMinimalSpecialFiber_a₄ :
    (SourcePsiMathlibMinimalSpecialFiber S v).a₄ =
      IsLocalRing.residue (SourcePsiMathlibMinimalBaseRing S v)
        (SourcePsiMathlibMinimalIntegralCurve S v).a₄ := by
  rw [SourcePsiMathlibMinimalSpecialFiber,
    SourcePsiMathlibMinimalReducedCurve,
    WeierstrassCurve.reduction, WeierstrassCurve.map_a₄]

theorem SourcePsiMathlibMinimalSpecialFiber_a₆ :
    (SourcePsiMathlibMinimalSpecialFiber S v).a₆ =
      IsLocalRing.residue (SourcePsiMathlibMinimalBaseRing S v)
        (SourcePsiMathlibMinimalIntegralCurve S v).a₆ := by
  rw [SourcePsiMathlibMinimalSpecialFiber,
    SourcePsiMathlibMinimalReducedCurve,
    WeierstrassCurve.reduction, WeierstrassCurve.map_a₆]

/-- Discriminant reduction law for the actual minimal special fiber. -/
theorem SourcePsiMathlibMinimalSpecialFiber_Δ :
    (SourcePsiMathlibMinimalSpecialFiber S v).Δ =
      IsLocalRing.residue (SourcePsiMathlibMinimalBaseRing S v)
        (SourcePsiMathlibMinimalIntegralCurve S v).Δ := by
  rw [SourcePsiMathlibMinimalSpecialFiber,
    SourcePsiMathlibMinimalReducedCurve,
    WeierstrassCurve.reduction, WeierstrassCurve.map_Δ]

/-- Good reduction is exactly ellipticity of the actual minimal special fiber. -/
theorem SourcePsiMathlibMinimalSpecialFiber_isElliptic_iff_goodReduction :
    (SourcePsiMathlibMinimalSpecialFiber S v).IsElliptic ↔
      HasGoodReduction (SourcePsiMathlibMinimalBaseRing S v)
        (SourcePsiMathlibMinimalCurve S v) :=
  (WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction
    (R := SourcePsiMathlibMinimalBaseRing S v)
    (W := SourcePsiMathlibMinimalCurve S v)).symm

/-- Non-elliptic minimal reduction implies the residue discriminant vanishes. -/
theorem SourcePsiMathlibMinimalSpecialFiber_Δ_eq_zero_of_not_goodReduction
    (h : ¬ HasGoodReduction (SourcePsiMathlibMinimalBaseRing S v)
      (SourcePsiMathlibMinimalCurve S v)) :
    (SourcePsiMathlibMinimalSpecialFiber S v).Δ = 0 := by
  have hnot : ¬ (SourcePsiMathlibMinimalSpecialFiber S v).IsElliptic :=
    fun hE => h
      ((SourcePsiMathlibMinimalSpecialFiber_isElliptic_iff_goodReduction S v).mp hE)
  exact WeierstrassCurve.Δ_eq_zero_of_not_isElliptic hnot

/-- Elliptic/singular dichotomy from the residue discriminant. -/
theorem SourcePsiMathlibMinimalSpecialFiber_elliptic_or_Δ_zero :
    (SourcePsiMathlibMinimalSpecialFiber S v).IsElliptic ∨
      (SourcePsiMathlibMinimalSpecialFiber S v).Δ = 0 := by
  by_cases hΔ : (SourcePsiMathlibMinimalSpecialFiber S v).Δ = 0
  · exact Or.inr hΔ
  · exact Or.inl ((SourcePsiMathlibMinimalSpecialFiber S v).isElliptic_iff.mpr hΔ)

/-- Good reduction gives an elliptic minimal special fiber. -/
theorem SourcePsiMathlibMinimalSpecialFiber_isElliptic_of_goodReduction
    (h : HasGoodReduction (SourcePsiMathlibMinimalBaseRing S v)
      (SourcePsiMathlibMinimalCurve S v)) :
    (SourcePsiMathlibMinimalSpecialFiber S v).IsElliptic :=
  (SourcePsiMathlibMinimalSpecialFiber_isElliptic_iff_goodReduction S v).mpr h

/-- Elliptic minimal special fiber gives good reduction. -/
theorem SourcePsiMathlibMinimalSpecialFiber_goodReduction_of_isElliptic
    (h : (SourcePsiMathlibMinimalSpecialFiber S v).IsElliptic) :
    HasGoodReduction (SourcePsiMathlibMinimalBaseRing S v)
      (SourcePsiMathlibMinimalCurve S v) :=
  (SourcePsiMathlibMinimalSpecialFiber_isElliptic_iff_goodReduction S v).mp h

/-- Exact actual minimal special-fiber statement: the special fiber is Mathlib's
reduction, equals the reduced integral curve, and satisfies the elliptic/singular
dichotomy. -/
def SourcePsiMathlibMinimalSpecialFiberStatement : Prop :=
  (SourcePsiMathlibMinimalSpecialFiber S v =
      SourcePsiMathlibMinimalReducedCurve S v) ∧
    ((SourcePsiMathlibMinimalSpecialFiber S v).IsElliptic ↔
      HasGoodReduction (SourcePsiMathlibMinimalBaseRing S v)
        (SourcePsiMathlibMinimalCurve S v)) ∧
      ((SourcePsiMathlibMinimalSpecialFiber S v).IsElliptic ∨
        (SourcePsiMathlibMinimalSpecialFiber S v).Δ = 0)

/-- The actual minimal special-fiber statement is proved. -/
theorem SourcePsiMathlibMinimalSpecialFiberStatement_iff :
    SourcePsiMathlibMinimalSpecialFiberStatement S v :=
  ⟨SourcePsiMathlibMinimalSpecialFiber_eq_reducedCurve S v,
    SourcePsiMathlibMinimalSpecialFiber_isElliptic_iff_goodReduction S v,
    SourcePsiMathlibMinimalSpecialFiber_elliptic_or_Δ_zero S v⟩

/-! ## Exact residual for the actual minimal special fiber

Constructed/proved:
- Mathlib's actual minimal curve W.minimal R for the source base-changed curve;
- its integral model integralModel R (W.minimal R);
- the actual special fiber (W.minimal R).reduction R;
- equality with the residue map of the integral minimal model;
- all five coefficient reductions and the discriminant reduction;
- good reduction iff elliptic;
- bad reduction gives vanishing residue discriminant;
- elliptic/singular dichotomy from the residue discriminant.

Still missing:
1. identification with an actual source special fiber beyond the Mathlib
   reduction equality;
2. properness/regularity of the integral minimal model;
3. component/node data and split multiplicative/additive refinement;
4. stable reduction type and compatibility with the source contract.

These are exact residual objects.  No source special fiber is fabricated.
-/
end LeanFormal.IUT.SourcePsiActualMinimalSpecialFiber

end
