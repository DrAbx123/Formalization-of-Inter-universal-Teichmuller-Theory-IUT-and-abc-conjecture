/-
  Actual special fiber and source reduction API for the Mathlib minimal model.

  This file uses Mathlib's actual minimal curve
  Wmin = (SourcePsiBaseChangedCurve).minimal R, its integral model
  integralModel R Wmin, and its reduction (Wmin).reduction R.  It packages:
  * coefficient and discriminant comparisons for the actual special fiber;
  * the good/multiplicative/additive reduction trichotomy;
  * the elliptic/singular dichotomy from the residue discriminant;
  * the actual source-reduction predicates induced by the Mathlib classes.

  No special fiber, reduction type, or component is fabricated.  Split
  multiplicative refinement and component data remain exact residual.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiActualMinimalSpecialFiber
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiActualSpecialFiber

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelReduction
open LeanFormal.IUT.SourcePsiReductionSpecialFiber
open LeanFormal.IUT.SourcePsiReductionActualConstruct
open LeanFormal.IUT.SourcePsiResidueRingFinite
open LeanFormal.IUT.AdicCompletionFractionField
open LeanFormal.IUT.SourcePsiActualMinimalSpecialFiber
open LeanFormal.IUT.SourcePsiMinimalModelCriterion
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- The actual minimal special fiber, named for the source reduction API. -/
abbrev SourcePsiActualSpecialFiber : WeierstrassCurve (SourcePsiResidueField S v) :=
  SourcePsiMathlibMinimalSpecialFiber S v

/-- The actual minimal model curve over K. -/
abbrev SourcePsiActualMinimalBaseCurve :
    WeierstrassCurve (SourcePsiMathlibMinimalFractionField S v) :=
  SourcePsiMathlibMinimalCurve S v

/-- The actual minimal integral curve over R. -/
abbrev SourcePsiActualMinimalIntegralCurve :
    WeierstrassCurve (SourcePsiMathlibMinimalBaseRing S v) :=
  SourcePsiMathlibMinimalIntegralCurve S v

/-- Actual good reduction of the source base curve. -/
abbrev SourcePsiActualGoodReduction : Prop :=
  HasGoodReduction (SourcePsiMathlibMinimalBaseRing S v)
    (SourcePsiActualMinimalBaseCurve S v)

/-- Actual multiplicative reduction of the source base curve. -/
abbrev SourcePsiActualMultiplicativeReduction : Prop :=
  HasMultiplicativeReduction (SourcePsiMathlibMinimalBaseRing S v)
    (SourcePsiActualMinimalBaseCurve S v)

/-- Actual additive reduction of the source base curve. -/
abbrev SourcePsiActualAdditiveReduction : Prop :=
  HasAdditiveReduction (SourcePsiMathlibMinimalBaseRing S v)
    (SourcePsiActualMinimalBaseCurve S v)

/-- Actual split multiplicative reduction. -/
abbrev SourcePsiActualSplitMultiplicativeReduction : Prop :=
  HasSplitMultiplicativeReduction (SourcePsiMathlibMinimalBaseRing S v)
    (SourcePsiActualMinimalBaseCurve S v)

/-- Special-fiber identification with the residue map of the actual minimal
integral model. -/
theorem SourcePsiActualSpecialFiber_eq_reducedCurve :
    SourcePsiActualSpecialFiber S v =
      SourcePsiMathlibMinimalReducedCurve S v :=
  SourcePsiMathlibMinimalSpecialFiber_eq_reducedCurve S v

/-- Coefficient a1 of the actual special fiber. -/
theorem SourcePsiActualSpecialFiber_a₁ :
    (SourcePsiActualSpecialFiber S v).a₁ =
      IsLocalRing.residue (SourcePsiMathlibMinimalBaseRing S v)
        (SourcePsiActualMinimalIntegralCurve S v).a₁ :=
  SourcePsiMathlibMinimalSpecialFiber_a₁ S v

theorem SourcePsiActualSpecialFiber_a₂ :
    (SourcePsiActualSpecialFiber S v).a₂ =
      IsLocalRing.residue (SourcePsiMathlibMinimalBaseRing S v)
        (SourcePsiActualMinimalIntegralCurve S v).a₂ :=
  SourcePsiMathlibMinimalSpecialFiber_a₂ S v

theorem SourcePsiActualSpecialFiber_a₃ :
    (SourcePsiActualSpecialFiber S v).a₃ =
      IsLocalRing.residue (SourcePsiMathlibMinimalBaseRing S v)
        (SourcePsiActualMinimalIntegralCurve S v).a₃ :=
  SourcePsiMathlibMinimalSpecialFiber_a₃ S v

theorem SourcePsiActualSpecialFiber_a₄ :
    (SourcePsiActualSpecialFiber S v).a₄ =
      IsLocalRing.residue (SourcePsiMathlibMinimalBaseRing S v)
        (SourcePsiActualMinimalIntegralCurve S v).a₄ :=
  SourcePsiMathlibMinimalSpecialFiber_a₄ S v

theorem SourcePsiActualSpecialFiber_a₆ :
    (SourcePsiActualSpecialFiber S v).a₆ =
      IsLocalRing.residue (SourcePsiMathlibMinimalBaseRing S v)
        (SourcePsiActualMinimalIntegralCurve S v).a₆ :=
  SourcePsiMathlibMinimalSpecialFiber_a₆ S v

/-- Discriminant of the actual special fiber. -/
theorem SourcePsiActualSpecialFiber_Δ :
    (SourcePsiActualSpecialFiber S v).Δ =
      IsLocalRing.residue (SourcePsiMathlibMinimalBaseRing S v)
        (SourcePsiActualMinimalIntegralCurve S v).Δ :=
  SourcePsiMathlibMinimalSpecialFiber_Δ S v

/-- c4 reduction for the actual special fiber. -/
theorem SourcePsiActualSpecialFiber_c₄ :
    (SourcePsiActualSpecialFiber S v).c₄ =
      IsLocalRing.residue (SourcePsiMathlibMinimalBaseRing S v)
        (SourcePsiActualMinimalIntegralCurve S v).c₄ := by
  rw [SourcePsiActualSpecialFiber, SourcePsiMathlibMinimalSpecialFiber,
    SourcePsiMathlibMinimalReducedCurve,
    WeierstrassCurve.reduction, WeierstrassCurve.map_c₄]

/-- c6 reduction for the actual special fiber. -/
theorem SourcePsiActualSpecialFiber_c₆ :
    (SourcePsiActualSpecialFiber S v).c₆ =
      IsLocalRing.residue (SourcePsiMathlibMinimalBaseRing S v)
        (SourcePsiActualMinimalIntegralCurve S v).c₆ := by
  rw [SourcePsiActualSpecialFiber, SourcePsiMathlibMinimalSpecialFiber,
    SourcePsiMathlibMinimalReducedCurve,
    WeierstrassCurve.reduction, WeierstrassCurve.map_c₆]

/-- Good reduction iff the actual special fiber is elliptic. -/
theorem SourcePsiActualSpecialFiber_goodReduction_iff_isElliptic :
    SourcePsiActualGoodReduction S v ↔
      (SourcePsiActualSpecialFiber S v).IsElliptic :=
  (SourcePsiMathlibMinimalSpecialFiber_isElliptic_iff_goodReduction S v).symm

/-- Actual special fiber is elliptic iff its residue discriminant is nonzero. -/
theorem SourcePsiActualSpecialFiber_isElliptic_iff_Δ_ne_zero :
    (SourcePsiActualSpecialFiber S v).IsElliptic ↔
      (SourcePsiActualSpecialFiber S v).Δ ≠ 0 :=
  (SourcePsiActualSpecialFiber S v).isElliptic_iff

/-- Actual special fiber is singular iff its residue discriminant vanishes. -/
theorem SourcePsiActualSpecialFiber_not_isElliptic_iff_Δ_eq_zero :
    ¬ (SourcePsiActualSpecialFiber S v).IsElliptic ↔
      (SourcePsiActualSpecialFiber S v).Δ = 0 := by
  rw [SourcePsiActualSpecialFiber_isElliptic_iff_Δ_ne_zero]

/-- Multiplicative reduction implies bad/elliptic obstruction. -/
theorem SourcePsiActualSpecialFiber_not_isElliptic_of_multiplicative
    (h : SourcePsiActualMultiplicativeReduction S v) :
    ¬ (SourcePsiActualSpecialFiber S v).IsElliptic :=
  fun hE => h.not_hasGoodReduction
    ((SourcePsiActualSpecialFiber_goodReduction_iff_isElliptic S v).mpr hE)

/-- Additive reduction implies bad/elliptic obstruction. -/
theorem SourcePsiActualSpecialFiber_not_isElliptic_of_additive
    (h : SourcePsiActualAdditiveReduction S v) :
    ¬ (SourcePsiActualSpecialFiber S v).IsElliptic :=
  fun hE => h.not_hasGoodReduction
    ((SourcePsiActualSpecialFiber_goodReduction_iff_isElliptic S v).mpr hE)

/-- Multiplicative reduction makes the residue discriminant vanish. -/
theorem SourcePsiActualSpecialFiber_Δ_eq_zero_of_multiplicative
    (h : SourcePsiActualMultiplicativeReduction S v) :
    (SourcePsiActualSpecialFiber S v).Δ = 0 :=
  (SourcePsiActualSpecialFiber_not_isElliptic_iff_Δ_eq_zero S v).mp
    (SourcePsiActualSpecialFiber_not_isElliptic_of_multiplicative S v h)

/-- Additive reduction makes the residue discriminant vanish. -/
theorem SourcePsiActualSpecialFiber_Δ_eq_zero_of_additive
    (h : SourcePsiActualAdditiveReduction S v) :
    (SourcePsiActualSpecialFiber S v).Δ = 0 :=
  (SourcePsiActualSpecialFiber_not_isElliptic_iff_Δ_eq_zero S v).mp
    (SourcePsiActualSpecialFiber_not_isElliptic_of_additive S v h)

/-- Actual good/multiplicative/additive reduction trichotomy. -/
theorem SourcePsiActualSpecialFiber_reduction_trichotomy :
    SourcePsiActualGoodReduction S v ∨
      SourcePsiActualMultiplicativeReduction S v ∨
        SourcePsiActualAdditiveReduction S v :=
  WeierstrassCurve.hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction
    (R := SourcePsiMathlibMinimalBaseRing S v)
    (W := SourcePsiActualMinimalBaseCurve S v)

/-- Exact actual reduction type data: the three Mathlib reduction classes for the
actual minimal curve. -/
structure SourcePsiActualReductionTypeData where
  good : Prop
  multiplicative : Prop
  additive : Prop
  good_iff_elliptic : good ↔ (SourcePsiActualSpecialFiber S v).IsElliptic
  multiplicative_bad : multiplicative → (SourcePsiActualSpecialFiber S v).Δ = 0
  additive_bad : additive → (SourcePsiActualSpecialFiber S v).Δ = 0
  trichotomy : good ∨ multiplicative ∨ additive

/-- The actual reduction type data from Mathlib's reduction classes. -/
def SourcePsiActualReductionTypeData.ofMinimalModel :
    SourcePsiActualReductionTypeData S v where
  good := SourcePsiActualGoodReduction S v
  multiplicative := SourcePsiActualMultiplicativeReduction S v
  additive := SourcePsiActualAdditiveReduction S v
  good_iff_elliptic :=
    (SourcePsiActualSpecialFiber_goodReduction_iff_isElliptic S v).symm
  multiplicative_bad :=
    SourcePsiActualSpecialFiber_Δ_eq_zero_of_multiplicative S v
  additive_bad :=
    SourcePsiActualSpecialFiber_Δ_eq_zero_of_additive S v
  trichotomy :=
    SourcePsiActualSpecialFiber_reduction_trichotomy S v

/-- Exact reduction statement for the actual minimal special fiber. -/
def SourcePsiActualSpecialFiberReductionStatement : Prop :=
  (SourcePsiActualSpecialFiber S v =
      SourcePsiMathlibMinimalReducedCurve S v) ∧
    ((SourcePsiActualSpecialFiber S v).IsElliptic ↔
      SourcePsiActualGoodReduction S v) ∧
      (SourcePsiActualSpecialFiber S v).Δ = 0 ∨
        ¬ (SourcePsiActualSpecialFiber S v).Δ = 0

/-- The actual special-fiber reduction statement is proved. -/
theorem SourcePsiActualSpecialFiberReductionStatement_iff :
    SourcePsiActualSpecialFiberReductionStatement S v :=
  ⟨SourcePsiActualSpecialFiber_eq_reducedCurve S v,
    SourcePsiActualSpecialFiber_goodReduction_iff_isElliptic S v,
    em ((SourcePsiActualSpecialFiber S v).Δ = 0)⟩



/-- b2 reduction for the actual special fiber. -/
theorem SourcePsiActualSpecialFiber_b₂ :
    (SourcePsiActualSpecialFiber S v).b₂ =
      IsLocalRing.residue (SourcePsiMathlibMinimalBaseRing S v)
        (SourcePsiActualMinimalIntegralCurve S v).b₂ := by
  rw [SourcePsiActualSpecialFiber, SourcePsiMathlibMinimalSpecialFiber,
    SourcePsiMathlibMinimalReducedCurve,
    WeierstrassCurve.reduction, WeierstrassCurve.map_b₂]

/-- b4 reduction for the actual special fiber. -/
theorem SourcePsiActualSpecialFiber_b₄ :
    (SourcePsiActualSpecialFiber S v).b₄ =
      IsLocalRing.residue (SourcePsiMathlibMinimalBaseRing S v)
        (SourcePsiActualMinimalIntegralCurve S v).b₄ := by
  rw [SourcePsiActualSpecialFiber, SourcePsiMathlibMinimalSpecialFiber,
    SourcePsiMathlibMinimalReducedCurve,
    WeierstrassCurve.reduction, WeierstrassCurve.map_b₄]

/-- b6 reduction for the actual special fiber. -/
theorem SourcePsiActualSpecialFiber_b₆ :
    (SourcePsiActualSpecialFiber S v).b₆ =
      IsLocalRing.residue (SourcePsiMathlibMinimalBaseRing S v)
        (SourcePsiActualMinimalIntegralCurve S v).b₆ := by
  rw [SourcePsiActualSpecialFiber, SourcePsiMathlibMinimalSpecialFiber,
    SourcePsiMathlibMinimalReducedCurve,
    WeierstrassCurve.reduction, WeierstrassCurve.map_b₆]

/-- b8 reduction for the actual special fiber. -/
theorem SourcePsiActualSpecialFiber_b₈ :
    (SourcePsiActualSpecialFiber S v).b₈ =
      IsLocalRing.residue (SourcePsiMathlibMinimalBaseRing S v)
        (SourcePsiActualMinimalIntegralCurve S v).b₈ := by
  rw [SourcePsiActualSpecialFiber, SourcePsiMathlibMinimalSpecialFiber,
    SourcePsiMathlibMinimalReducedCurve,
    WeierstrassCurve.reduction, WeierstrassCurve.map_b₈]

/-- Nonzero residue discriminant iff good reduction. -/
theorem SourcePsiActualSpecialFiber_Δ_ne_zero_iff_goodReduction :
    (SourcePsiActualSpecialFiber S v).Δ ≠ 0 ↔
      SourcePsiActualGoodReduction S v :=
  (SourcePsiActualSpecialFiber_isElliptic_iff_Δ_ne_zero S v).symm.trans
    (SourcePsiActualSpecialFiber_goodReduction_iff_isElliptic S v).symm

/-- Good reduction gives nonzero residue discriminant. -/
theorem SourcePsiActualSpecialFiber_Δ_ne_zero_of_goodReduction
    (h : SourcePsiActualGoodReduction S v) :
    (SourcePsiActualSpecialFiber S v).Δ ≠ 0 :=
  (SourcePsiActualSpecialFiber_Δ_ne_zero_iff_goodReduction S v).mpr h

/-- Zero residue discriminant is exactly bad reduction. -/
theorem SourcePsiActualSpecialFiber_not_goodReduction_of_Δ_eq_zero
    (h : (SourcePsiActualSpecialFiber S v).Δ = 0) :
    ¬ SourcePsiActualGoodReduction S v :=
  fun hgood => (SourcePsiActualSpecialFiber_Δ_ne_zero_of_goodReduction S v hgood) h

/-! ## Exact actual special-fiber residual

Proved:
- actual special fiber is Mathlib's reduction of the actual minimal model and
  equals the reduced integral curve;
- coefficient a1,a2,a3,a4,a6 reductions and Delta,c4,c6 reductions;
- good reduction iff elliptic; elliptic iff residue discriminant nonzero;
- singular iff residue discriminant zero;
- multiplicative/additive reductions are bad and force zero residue discriminant;
- Mathlib good/multiplicative/additive trichotomy for the actual minimal curve;
- actual reduction-type data packaging.

Still missing:
1. split multiplicative refinement over the residue field;
2. properness/regularity of the actual integral minimal model;
3. component/node graph of the special fiber;
4. stable reduction type and source-contract comparison;
5. identification with a source special fiber beyond Mathlib reduction equality.

These are exact residual objects.  No special fiber or component is fabricated.
-/
end LeanFormal.IUT.SourcePsiActualSpecialFiber

end